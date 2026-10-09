import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelSeamPorts
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelPlugMap
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelPlugCut

/-!
# Chapter-14 assembly, relative COMPARE shared seams: drilled pieces and the seam bands in `W`

Lane ASM-L2e3, shared seam group (for G5 SEP and G6 NONSEP). A drilled carrier `L` embedded in the
capped carrier `Q` by `η` (bijective differentials) is a piece of `W` through `F ∘ Ψ⁻¹ ∘ η`, once
`Ψ⁻¹ ∘ η` lands in the source of the fold `F` (`exists_drilledPiece`; injective). For tubes `φ t`
whose closed tubes of radius `1 + κ` are pairwise disjoint (`eventually_tubeImage_pairwiseDisjoint`)
and caps inside the radius `1 - ν` tubes (`hsrc`), the seam bands read through `Ψ⁻¹` lie in the
source of `F` (`tubeBand_mem_source`), the seams of two tubes are disjoint
(`tubeSeamCollar_target_disjoint`), and a point of `Q` fixed by `Ψ` off the radius `1 + κ` tubes is
sent off every seam (`not_mem_tubeSeamCollar_target`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **A drilled carrier is an injective piece of `W`** through `F ∘ Ψ⁻¹ ∘ η`. -/
theorem exists_drilledPiece {W Q : CompactCarrier.{u}}
    (F : PartialDiffeomorph Q.model W.model Q.Carrier W.Carrier ∞)
    (Ψ : Q.Carrier ≃ₘ⟮Q.model, Q.model⟯ Q.Carrier) (L : CompactCarrier.{u})
    (hLk : L.kind = .withBoundary) [ConnectedSpace L.Carrier] (η : L.Carrier → Q.Carrier)
    (hη : IsSmoothEmbedding L.model Q.model ∞ η)
    (hηb : ∀ x, Bijective (mfderiv L.model Q.model η x))
    (hsrc : ∀ x, Ψ.symm (η x) ∈ F.source) :
    ∃ (A : PieceFold W) (e : L.Carrier ≃ₘ⟮L.model, 𝓡∂ 3⟯ A.Piece),
      (∀ x, A.map (e x) = F (Ψ.symm (η x))) ∧ Injective A.map := by
  have hf : ContMDiff L.model W.model ∞ (fun x => F (Ψ.symm (η x))) :=
    F.contMDiffOn.comp_contMDiff (Ψ.symm.contMDiff.comp hη.contMDiff) hsrc
  have hb : ∀ x, Bijective (mfderiv L.model W.model (fun x => F (Ψ.symm (η x))) x) := by
    intro x
    have h1 : MDifferentiableAt L.model Q.model η x := hη.contMDiff.mdifferentiableAt (by simp)
    have h2 : MDifferentiableAt Q.model Q.model Ψ.symm (η x) :=
      Ψ.symm.contMDiff.mdifferentiableAt (by simp)
    have h3 : MDifferentiableAt Q.model W.model F (Ψ.symm (η x)) :=
      F.mdifferentiableAt (by simp) (hsrc x)
    have hb12 := bijective_mfderiv_comp h1 h2 (hηb x) (bijective_mfderiv_diffeomorph Ψ.symm _)
    exact bijective_mfderiv_comp (h2.comp x h1) h3 hb12 (bijective_mfderiv_of_mem_source F (hsrc x))
  obtain ⟨A, e, hA⟩ := exists_pieceFold_of_carrier L hLk _ hf hb
  refine ⟨A, e, hA, fun a b hab => ?_⟩
  rw [← e.apply_symm_apply a, ← e.apply_symm_apply b, hA, hA] at hab
  have h := hη.isEmbedding.injective (Ψ.symm.injective
    (F.toPartialEquiv.injOn (hsrc _) (hsrc _) hab))
  rw [← e.apply_symm_apply a, ← e.apply_symm_apply b, h]

/-! ### The seam bands in `W` -/

theorem tubeBand_subset_le (κ : ℝ) :
    tubeBand.{u} κ ⊆ {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1 + κ} :=
  fun _ hp => hp.2.le

section Bands

variable {W Q : CompactCarrier.{u}}
  (F : PartialDiffeomorph Q.model W.model Q.Carrier W.Carrier ∞)
  (Ψ : Q.Carrier ≃ₘ⟮Q.model, Q.model⟯ Q.Carrier) {k : ℕ}
  (φ : Fin k → PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) Q.model (PlaneLift.{u} × Circle) Q.Carrier ∞)

theorem tubeBand_subset_source (h3 : ∀ t, {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ (φ t).source)
    {κ : ℝ} (hκ : κ ≤ 2) (t : Fin k) : tubeBand κ ⊆ (φ t).source := fun p hp =>
  h3 t (show ‖p.1.down‖ ≤ 3 by linarith [hp.2])

/-- A point of `Q` off the open unit tubes is sent by `Ψ⁻¹` into the source of `F`. -/
theorem symm_mem_source_of_not_mem_tubes {ν : ℝ} (hν : 0 < ν)
    (hsrc : ∀ x, Ψ x ∉ ⋃ t, φ t '' {p | ‖p.1.down‖ < 1 - ν} → x ∈ F.source) {y : Q.Carrier}
    (hy : y ∉ ⋃ t, φ t '' {p | ‖p.1.down‖ < 1}) : Ψ.symm y ∈ F.source := by
  apply hsrc
  rw [Ψ.apply_symm_apply]
  intro h
  obtain ⟨t, p, hp, rfl⟩ := mem_iUnion.mp h
  exact hy (mem_iUnion.mpr ⟨t, p, show ‖p.1.down‖ < 1 by linarith [show ‖p.1.down‖ < 1 - ν from hp],
    rfl⟩)

/-- **The seam bands lie in the source of `F`.** -/
theorem tubeBand_mem_source (h3 : ∀ t, {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ (φ t).source)
    {ν κ : ℝ} (hν : 0 < ν) (hκ : 0 < κ) (hκν : κ ≤ ν) (hκ2 : κ ≤ 2)
    (hw : Pairwise fun t t' =>
      Disjoint (φ t '' {p | ‖p.1.down‖ ≤ 1 + κ}) (φ t' '' {p | ‖p.1.down‖ ≤ 1 + κ}))
    (hsrc : ∀ x, Ψ x ∉ ⋃ t, φ t '' {p | ‖p.1.down‖ < 1 - ν} → x ∈ F.source) (t : Fin k)
    {p : PlaneLift.{u} × Circle} (hp : p ∈ tubeBand κ) : Ψ.symm (φ t p) ∈ F.source := by
  apply hsrc
  rw [Ψ.apply_symm_apply]
  intro h
  obtain ⟨t', q, hq, hqp⟩ := mem_iUnion.mp h
  have hq' : ‖q.1.down‖ < 1 - ν := hq
  by_cases htt : t' = t
  · subst htt
    have hqs : q ∈ (φ t').source := h3 t' (show ‖q.1.down‖ ≤ 3 by linarith)
    have hpq := (φ t').toPartialEquiv.injOn hqs (tubeBand_subset_source φ h3 hκ2 t' hp) hqp
    have h1 : 1 - κ < ‖p.1.down‖ := hp.1
    rw [← hpq] at h1
    linarith
  · exact disjoint_left.mp (hw htt) ⟨q, show ‖q.1.down‖ ≤ 1 + κ by linarith, hqp⟩
      ⟨p, tubeBand_subset_le κ hp, rfl⟩

variable {κ : ℝ} (hκ : 0 < κ)

/-- **Two seams are disjoint.** -/
theorem tubeSeamCollar_target_disjoint (hκ1 : κ < 1)
    (hw : Pairwise fun t t' =>
      Disjoint (φ t '' {p | ‖p.1.down‖ ≤ 1 + κ}) (φ t' '' {p | ‖p.1.down‖ ≤ 1 + κ}))
    {t t' : Fin k} (htt : t ≠ t') :
    Disjoint (tubeSeamCollar F Ψ (φ t) hκ).target (tubeSeamCollar F Ψ (φ t') hκ).target := by
  refine disjoint_left.mpr fun y hy hy' => ?_
  obtain ⟨p, hp, -, hpF, rfl⟩ := mem_tubeSeamCollar_target F Ψ (φ t) hκ hκ1 hy
  obtain ⟨p', hp', -, hpF', he⟩ := mem_tubeSeamCollar_target F Ψ (φ t') hκ hκ1 hy'
  have h := Ψ.symm.injective (F.toPartialEquiv.injOn hpF hpF' he)
  exact disjoint_left.mp (hw htt) ⟨p, tubeBand_subset_le κ hp, rfl⟩
    ⟨p', tubeBand_subset_le κ hp', h.symm⟩

/-- **A point fixed by `Ψ` off the radius `1 + κ` tube is sent off the seam.** -/
theorem not_mem_tubeSeamCollar_target (hκ1 : κ < 1) (t : Fin k) {x : Q.Carrier}
    (hx : x ∈ F.source) (hΨx : Ψ x = x) (hxt : x ∉ φ t '' {p | ‖p.1.down‖ ≤ 1 + κ}) :
    F x ∉ (tubeSeamCollar F Ψ (φ t) hκ).target := by
  intro hy
  obtain ⟨p, hp, -, hpF, he⟩ := mem_tubeSeamCollar_target F Ψ (φ t) hκ hκ1 hy
  have h := F.toPartialEquiv.injOn hx hpF he
  have h' : Ψ x = φ t p := by
    change x = Ψ.symm (φ t p) at h
    rw [h, Ψ.apply_symm_apply]
  rw [hΨx] at h'
  exact hxt ⟨p, tubeBand_subset_le κ hp, h'.symm⟩

end Bands

/-- **The seams of finitely many placed tubes** (consumer of the width, band and seam lemmas): a
width `κ` and pairwise disjoint torus seams `σ t = tubeSeam` of `W`, each the band of radii
`(1 - κ, 1 + κ)` of `φ t` read through `Ψ⁻¹` and `F`. -/
theorem exists_tubeSeams {W Q : CompactCarrier.{u}}
    (F : PartialDiffeomorph Q.model W.model Q.Carrier W.Carrier ∞)
    (Ψ : Q.Carrier ≃ₘ⟮Q.model, Q.model⟯ Q.Carrier) {k : ℕ}
    (φ : Fin k → PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) Q.model (PlaneLift.{u} × Circle) Q.Carrier ∞)
    (h3 : ∀ t, {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ (φ t).source)
    (hφI : ∀ t, (φ t).target ⊆ Q.interior)
    (hd : Pairwise fun t t' =>
      Disjoint (φ t '' {p | ‖p.1.down‖ ≤ 1}) (φ t' '' {p | ‖p.1.down‖ ≤ 1}))
    {ν : ℝ} (hν : 0 < ν)
    (hsrc : ∀ x, Ψ x ∉ ⋃ t, φ t '' {p | ‖p.1.down‖ < 1 - ν} → x ∈ F.source) :
    ∃ (κ : ℝ) (hκ : 0 < κ), κ < 1 ∧ 2 * κ ≤ ν ∧ 2 * κ ≤ 1 ∧
      (Pairwise fun t t' =>
        Disjoint (φ t '' {p | ‖p.1.down‖ ≤ 1 + κ}) (φ t' '' {p | ‖p.1.down‖ ≤ 1 + κ})) ∧
      ∃ σ : Fin k → TorusSeam W, (∀ t, (σ t).collar = tubeSeamCollar F Ψ (φ t) hκ) ∧
        Pairwise fun t t' => Disjoint (σ t).collar.target (σ t').collar.target := by
  have hev := (eventually_tubeImage_pairwiseDisjoint φ h3 hd).and
    ((Ioo_mem_nhdsGT (show (0 : ℝ) < min (ν / 2) (1 / 2) by positivity)))
  obtain ⟨κ, ⟨hw, hκ0, hκm⟩, hκpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have hκ : (0 : ℝ) < κ := hκpos
  have hκν : κ ≤ ν / 2 := le_trans hκm.le (min_le_left _ _)
  have hκh : κ ≤ 1 / 2 := le_trans hκm.le (min_le_right _ _)
  have hκ1 : κ < 1 := by linarith
  have hB : ∀ t, tubeBand κ ⊆ (φ t).source := fun t => tubeBand_subset_source φ h3 (by linarith) t
  have hBF : ∀ t, ∀ p ∈ tubeBand κ, Ψ.symm (φ t p) ∈ F.source := fun t p hp =>
    tubeBand_mem_source F Ψ φ h3 hν hκ (by linarith) (by linarith) hw hsrc t hp
  refine ⟨κ, hκ, hκ1, by linarith, by linarith, hw,
    fun t => tubeSeam F Ψ (φ t) hκ hκ1 (hB t) (hBF t) (hφI t), fun t => rfl, fun t t' htt => ?_⟩
  exact tubeSeamCollar_target_disjoint F Ψ φ hκ hκ1 hw htt

end GC.GraphManifold.Assembly
