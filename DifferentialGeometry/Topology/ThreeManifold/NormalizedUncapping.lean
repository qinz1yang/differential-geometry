import DifferentialGeometry.Topology.ThreeManifold.UncappingReparametrization
import DifferentialGeometry.Topology.ThreeManifold.CapNormalization

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SphericalCapping

universe u
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "Annulus" => S2 × Icc (1 / 4 : ℝ) 1
local notation "CI" => ModelWithCorners.prod (𝓡 2) (𝓡∂ 1)
local notation "Cylinder" => S2 × unitInterval

private local instance capClosedCellCharts : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) := Handle.closedCellChartedSpaceSucc 2
private local instance capClosedCellSmooth : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) := Handle.closedCellIsManifold 2

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem exists_normalized_uncapping_homeomorph (v : S2) :
    ∃ (B : T.Boundary → ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
      (hsmall : ∀ b (x : ClosedCell 3), ‖x.val‖ ≤ 1 / 4 → B b x = x)
      (hboundary : ∀ b z, B b (sphereToClosedCell z) = sphereToClosedCell z),
      (∀ b (x : ClosedCell 3), ‖x.val‖ ≤ 1 / 2 → B b x = x) ∧
      (∀ b, ∃ e : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) (C.cap b ∘ sphereToClosedCell),
        (∃ he : e.radius ≤ 1 / 2, ∀ (p : S2 × symmetricOpenInterval e.radius) (hp : 0 ≤ p.2.val),
          e.toFun p = C.coreInclusionHalfCollar b
            (p.1, ⟨p.2.val, hp, p.2.property.2.trans_le he⟩)) ∧
        ∃ V : Set E3, IsOpen V ∧ sphere (0 : E3) 1 ⊆ V ∧
          (∀ x : ClosedCell 3, x.val ∈ V → x.val ∈ (e.reverse.radialPartialDiffeomorph v).source ∧
            C.cap b (B b x) = e.reverse.radialPartialDiffeomorph v x.val) ∧
          (∀ x : ClosedCell 3, x.val ∈ V →
            C.coreBoundaryExtension b e v (C.cap b (B b x)) =
              T.radialTube b.1 (C.attaching b) b.2 v x.val) ∧
          ∀ z : S2, IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (C.coreBoundaryExtension b e v)
            (C.cap b (sphereToClosedCell z))) ∧
      ∃ (Ψ : T.Index → Cylinder ≃ₘ⟮CI, CI⟯ Cylinder) (ρ : ℝ ≃ₘ[ℝ] ℝ)
        (hρ : MapsTo ρ (Icc (1 / 4 : ℝ) 1) (Icc (0 : ℝ) 1)),
        ρ (1 / 4) = 0 ∧ ρ 1 = 1 ∧ (∀ r, 0 < deriv ρ r) ∧
        (∃ ε₀ ε₁ : ℝ, 0 < ε₀ ∧ 0 < ε₁ ∧
          (∀ r, |r - 1 / 4| ≤ ε₀ → ρ r = r - 1 / 4) ∧
          ∀ r, 1 - ε₁ ≤ r → ρ r = r) ∧
        (∀ a p, (Ψ a p).2 = p.2) ∧
        (∀ a (t : unitInterval), t.val ≤ 1 / 3 → ∀ z, Ψ a (z,t) = (C.attaching (a,false) z,t)) ∧
        (∀ a (t : unitInterval), 2 / 3 ≤ t.val → ∀ z, Ψ a (z,t) = (C.attaching (a,true) z,t)) ∧
        ∃ H : C.UncappingQuotient ≃ₜ M.Carrier,
          (∀ x : T.core, H (Quot.mk C.innerCapRelation
            (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
              (C.coreImageHomeomorph x))) = x.val) ∧
          ∀ q : Σ _b : T.Boundary, Annulus,
            H (Quot.mk C.innerCapRelation
              (C.puncturedCappingReparametrization (fun b => (B b).toHomeomorph) hsmall hboundary
                (adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap q))) =
              T.cylinderMap q.1.1 (Ψ q.1.1 (q.2.1,
                ⟨(1 + (if q.1.2 then ρ q.2.2.val else -ρ q.2.2.val)) / 2, by
                  have h := hρ q.2.2.property
                  cases q.1.2 <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
                    constructor <;> linarith [h.1,h.2]⟩)) := by
  choose B e hhalf hbd he V hVo hSV hcap hrad hlocal using fun b => C.exists_cap_normalization b v
  have hsmall (b : T.Boundary) (x : ClosedCell 3) (hx : ‖x.val‖ ≤ 1 / 4) : B b x = x :=
    hhalf b x (hx.trans (by norm_num))
  refine ⟨B, hsmall, hbd, hhalf, ?_, ?_⟩
  · intro b
    exact ⟨e b, he b, V b, hVo b, hSV b, hcap b, hrad b, hlocal b⟩
  · obtain ⟨Ψ,ρ,hρ,hzero,hone,hpos,hgerm,hp,hlo,hhi,F,_,hcore,hann,_,H,hH⟩ :=
      C.exists_uncapping_homeomorph
    let R := C.uncappingQuotientReparametrization (fun b => (B b).toHomeomorph) hsmall hbd
    refine ⟨Ψ,ρ,hρ,hzero,hone,hpos,hgerm,hp,hlo,hhi,R.symm.trans H,?_,?_⟩
    · intro x
      change H (R.symm (Quot.mk C.innerCapRelation
        (adjunctionLower (i := capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap
          (C.coreImageHomeomorph x)))) = _
      erw [C.uncappingQuotientReparametrization_symm_core, hH, hcore]
    · intro q
      change H (R.symm (Quot.mk C.innerCapRelation
        (C.puncturedCappingReparametrization (fun b => (B b).toHomeomorph) hsmall hbd
          (adjunctionCell (capAnnuliBoundaryInclusion (T := T)) C.capAnnuliAttachingMap q)))) = _
      erw [← C.uncappingQuotientReparametrization_mk]
      change H (R.symm (R _)) = _
      rw [R.symm_apply_apply, hH, hann]

end DifferentialGeometry.Topology.SphericalCapping
