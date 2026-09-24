import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Collar
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SelfAttachment

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
  (c d : BallChart 3 (𝓡 3) M)
  (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (a : Sphere (n := 3) ≃ₜ Sphere (n := 3))

def coreInterior : TopologicalSpace.Opens M :=
  ⟨(c.chart '' Metric.closedBall 0 1 ∪ d.chart '' Metric.closedBall 0 1)ᶜ,
    (c.isCompact_closedBall_image.isClosed.union d.isCompact_closedBall_image.isClosed).isOpen_compl⟩

def coreInteriorToCore (x : coreInterior c d) : c.DoublePunctured d :=
  ⟨x.val, by
    rintro (hc | hd)
    · exact x.property (Or.inl (Set.image_mono Metric.ball_subset_closedBall hc))
    · exact x.property (Or.inr (Set.image_mono Metric.ball_subset_closedBall hd))⟩

def coreInteriorInclusion : coreInterior c d → Quotient c d hcd a :=
  coreInclusion c d hcd a ∘ coreInteriorToCore c d

def bandInterior : TopologicalSpace.Opens (Sphere (n := 3) × ℝ) :=
  ⟨univ ×ˢ Ioo (0 : ℝ) 1, isOpen_univ.prod isOpen_Ioo⟩

def bandInteriorInclusion (p : bandInterior) : Quotient c d hcd a :=
  bandInclusion c d hcd a (p.val.1, ⟨p.val.2, p.property.2.1.le, p.property.2.2.le⟩)

def collarZero (z : Sphere (n := 3)) : CollarDomain :=
  (z, ⟨0, by constructor <;> norm_num [ConnectedSumQuotient.collarInterval]⟩)

theorem local_maps_cover (q : Quotient c d hcd a) :
    (∃ x, coreInteriorInclusion c d hcd a x = q) ∨
    (∃ x, bandInteriorInclusion c d hcd a x = q) ∨
    (∃ z, lowerCollar c d hcd a (collarZero z) = q) ∨
      ∃ z, upperCollar c d hcd a (collarZero z) = q := by
  induction q using Quot.inductionOn with
  | h p =>
    cases p with
    | inl b =>
      by_cases h0 : b.2.val = 0
      · right; right; left
        refine ⟨b.1, ?_⟩
        rw [collarZero, lowerCollar_zero]
        have hb : b = boundaryInclusion (false, b.1) := Prod.ext rfl (Subtype.ext h0)
        rw [hb]
        exact (seam_eq c d hcd a (false, b.1)).symm
      · by_cases h1 : b.2.val = 1
        · right; right; right
          refine ⟨b.1, ?_⟩
          rw [collarZero, upperCollar_zero]
          have hb : b = boundaryInclusion (true, b.1) := Prod.ext rfl (Subtype.ext h1)
          rw [hb]
          exact (seam_eq c d hcd a (true, b.1)).symm
        · right; left
          exact ⟨⟨(b.1, b.2.val), mem_univ _,
            lt_of_le_of_ne b.2.property.1 (Ne.symm h0), lt_of_le_of_ne b.2.property.2 h1⟩, rfl⟩
    | inr x =>
      by_cases hc : x.val ∈ c.chart '' Metric.closedBall 0 1
      · right; right; left
        obtain ⟨z, hz, hzx⟩ := hc
        have hzl : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
        have hzge : 1 ≤ ‖z‖ := by
          by_contra h
          exact x.property (Or.inl ⟨z, by simpa only [Metric.mem_ball, dist_zero_right] using not_le.mp h, hzx⟩)
        let w : Sphere (n := 3) := ⟨z, by rw [Metric.mem_sphere, dist_zero_right]; exact le_antisymm hzl hzge⟩
        refine ⟨w, ?_⟩
        rw [collarZero, lowerCollar_zero]
        exact congrArg (coreInclusion c d hcd a) (Subtype.ext hzx)
      · by_cases hd : x.val ∈ d.chart '' Metric.closedBall 0 1
        · right; right; right
          obtain ⟨z, hz, hzx⟩ := hd
          have hzl : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
          have hzge : 1 ≤ ‖z‖ := by
            by_contra h
            exact x.property (Or.inr ⟨z, by simpa only [Metric.mem_ball, dist_zero_right] using not_le.mp h, hzx⟩)
          let w : Sphere (n := 3) := ⟨z, by rw [Metric.mem_sphere, dist_zero_right]; exact le_antisymm hzl hzge⟩
          refine ⟨a.symm w, ?_⟩
          rw [collarZero, upperCollar_zero, a.apply_symm_apply]
          exact congrArg (coreInclusion c d hcd a) (Subtype.ext hzx)
        · left
          exact ⟨⟨x.val, not_or.mpr ⟨hc, hd⟩⟩, rfl⟩

variable [ChartedSpace E3 (Quotient c d hcd a)]

variable {P : Type*} [TopologicalSpace P] [ChartedSpace E3 P]

theorem isLocalDiffeomorph_of_comp_local_maps
    (hcl : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (coreInteriorInclusion c d hcd a))
    (hbl : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (bandInteriorInclusion c d hcd a))
    (hll : ∀ z, IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (lowerCollar c d hcd a) (collarZero z))
    (hul : ∀ z, IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (upperCollar c d hcd a) (collarZero z)) (F : Quotient c d hcd a → P)
    (hcore : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (F ∘ coreInteriorInclusion c d hcd a))
    (hband : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (F ∘ bandInteriorInclusion c d hcd a))
    (hlower : ∀ z, IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (F ∘ lowerCollar c d hcd a) (collarZero z))
    (hupper : ∀ z, IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (F ∘ upperCollar c d hcd a) (collarZero z)) : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ F := by
  intro x
  rcases local_maps_cover c d hcd a x with ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩
  · exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (hcore p) (hcl p)
  · exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (hband p) (hbl p)
  · exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (hlower p) (hll p)
  · exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (hupper p) (hul p)

end DifferentialGeometry.Topology.SelfAttachment
