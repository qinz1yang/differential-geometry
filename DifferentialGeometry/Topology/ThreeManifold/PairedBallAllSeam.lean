import DifferentialGeometry.Topology.ThreeManifold.PairedBallSeam

set_option autoImplicit false
noncomputable section
open Set Function Metric

namespace DifferentialGeometry.Topology.PairedBallGluing

universe u v w
variable {V : Type v} {E : Type w}
  (N : V → ConnectedClosedOrientedManifold.{u} 3)
  (endpoint : E → Bool → V)
  (chart : (e : E) → (b : Bool) →
    OrientedBallChart (N (endpoint e b)).toClosedOrientedManifold)
  (hdisj : Pairwise fun p q =>
    Disjoint (flagMap N endpoint chart p '' closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2)
      (flagMap N endpoint chart q '' closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2))
  (a : E → BoundaryAttachment)

def allCore [Finite E] : TopologicalSpace.Opens (Σ v, PuncturedFactor N endpoint chart v) :=
  ⟨(⋃ (e : E) (b : Bool), range (fun z =>
      (⟨endpoint e b, boundaryPoint N endpoint chart hdisj e b z⟩ :
        Σ v, PuncturedFactor N endpoint chart v)))ᶜ,
    (isClosed_iUnion_of_finite fun e => isClosed_iUnion_of_finite fun b =>
      (isCompact_range (continuous_sigmaMk.comp
        (continuous_boundaryPoint N endpoint chart hdisj e b))).isClosed).isOpen_compl⟩

def allCoreInclusion [Finite E] : allCore N endpoint chart hdisj →
    Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e (a e) x y) :=
  fun x => Quot.mk _ x.val

def allSeamChart (e : E) : SelfAttachment.directSeamDomain →
    Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e (a e) x y) :=
  Quot.map id (fun {_ _} h => ⟨e, h⟩) ∘ seamChart N endpoint chart hdisj e (a e)

theorem allSeamChart_nonneg (e : E) (p : SelfAttachment.directSeamDomain)
    (ht : 0 ≤ p.val.2) :
    allSeamChart N endpoint chart hdisj a e p =
      Quot.mk _ ⟨endpoint e false,
        radialPoint N endpoint chart hdisj e false p.val.1 (1 + p.val.2)
          ⟨by linarith, by linarith [p.property.2.2]⟩⟩ := by
  simp only [allSeamChart, comp_apply, seamChart, dite_eq_left ht]
  rfl

theorem allSeamChart_neg (e : E) (p : SelfAttachment.directSeamDomain)
    (ht : p.val.2 < 0) :
    allSeamChart N endpoint chart hdisj a e p =
      Quot.mk _ ⟨endpoint e true,
        radialPoint N endpoint chart hdisj e true ((a e).val p.val.1) (1 - p.val.2)
          ⟨by linarith, by linarith [p.property.2.1]⟩⟩ := by
  simp only [allSeamChart, comp_apply, seamChart, dite_eq_right (not_le.mpr ht)]
  rfl

theorem allSeamChart_zero (e : E) (z : SelfAttachment.Sphere (n := 3)) :
    allSeamChart N endpoint chart hdisj a e
      ⟨(z, 0), mem_univ _, by norm_num [SelfAttachment.directSeamDomain]⟩ =
      Quot.mk _ ⟨endpoint e false, boundaryPoint N endpoint chart hdisj e false z⟩ := by
  change Quot.map id (fun {_ _} h => ⟨e, h⟩)
    (seamChart N endpoint chart hdisj e (a e) _) = _
  rw [seamChart_zero]
  rfl

theorem all_local_maps_cover [Finite E]
    (q : Quot (fun x y => ∃ e, seamRel N endpoint chart hdisj e (a e) x y)) :
    (∃ x, allCoreInclusion N endpoint chart hdisj a x = q) ∨
      ∃ e z, allSeamChart N endpoint chart hdisj a e
        ⟨(z, 0), mem_univ _, by norm_num [SelfAttachment.directSeamDomain]⟩ = q := by
  classical
  induction q using Quot.inductionOn with
  | h x =>
    by_cases hx : x ∈ allCore N endpoint chart hdisj
    · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
    · right
      have hx' : x ∈ ⋃ (e : E) (b : Bool), range (fun z =>
          (⟨endpoint e b, boundaryPoint N endpoint chart hdisj e b z⟩ :
            Σ v, PuncturedFactor N endpoint chart v)) := not_not.mp hx
      obtain ⟨e, hx'⟩ := mem_iUnion.mp hx'
      obtain ⟨b, z, rfl⟩ := mem_iUnion.mp hx'
      cases b with
      | false => exact ⟨e, z, allSeamChart_zero N endpoint chart hdisj a e z⟩
      | true =>
        refine ⟨e, (a e).val.symm z, ?_⟩
        rw [allSeamChart_zero]
        apply Quot.sound
        refine ⟨e, (a e).val.symm z, Or.inl ⟨rfl, ?_⟩⟩
        rw [(a e).val.apply_symm_apply]

theorem range_allCoreInclusion_union_iUnion_range_allSeamChart [Finite E] :
    range (allCoreInclusion N endpoint chart hdisj a) ∪
      (⋃ e, range (allSeamChart N endpoint chart hdisj a e)) = univ := by
  apply eq_univ_of_forall
  intro q
  rcases all_local_maps_cover N endpoint chart hdisj a q with h | ⟨e, z, hz⟩
  · exact Or.inl h
  · exact Or.inr (mem_iUnion.mpr ⟨e, _, hz⟩)

end DifferentialGeometry.Topology.PairedBallGluing
