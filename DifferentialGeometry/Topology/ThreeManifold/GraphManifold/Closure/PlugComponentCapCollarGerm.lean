import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.PlugSideCapping

/-!
The same component cap charts recover the actual spherical half collars near radius one.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open DifferentialGeometry.Topology.Manifold GC.GraphManifold.MixedBoundaryCertificate
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.MixedBoundaryCertificate

private theorem capExtension_smul {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)
    (i : Fin B.sphereCount) (r : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    B.capBallAmbientExtension i (r • x) = r • B.capBallAmbientExtension i x := by
  rcases B.capBallAmbientExtension_choices i with hid | hneg
  · rw [hid]
    rfl
  · rw [hneg]
    change -(r • x) = r • -x
    exact smul_neg r x |>.symm

private theorem capExtension_sphere {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)
    (i : Fin B.sphereCount) (z : ClosureSphere.{u}) :
    B.capBallAmbientExtension i z.down.val =
      (B.sphereCapOrientationData.attaching i z).down.val := by
  have hv := B.capBallAmbientExtension_cell i (closureSphereToBall z)
  rw [B.sphereCapOrientationData.boundary] at hv
  exact hv

private theorem capExtension_polar {C : CompactCarrier.{u}} (B : MixedBoundaryCertificate C)
    (i : Fin B.sphereCount) (z : ClosureSphere.{u}) {r : ℝ} (hr : 0 < r) :
    boundedPlugSidePolar (B.capBallAmbientExtension i (r • z.down.val)) =
      (B.sphereCapOrientationData.attaching i z, r) := by
  rw [capExtension_smul, capExtension_sphere, boundedPlugSidePolar_apply]
  apply Prod.ext
  · exact congrArg ULift.up (sphereDirection_pos_smul SplitTube.poleS2
      (B.sphereCapOrientationData.attaching i z).down hr)
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hz : ‖(B.sphereCapOrientationData.attaching i z).down.val‖ = 1 :=
      mem_sphere_zero_iff_norm.mp (B.sphereCapOrientationData.attaching i z).down.property
    rw [hz, mul_one]

end GC.GraphManifold.MixedBoundaryCertificate

namespace GC.Seifert.ElementaryPresentation

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)
  (hlin : E.IsLinearSeam j)
  (d : PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞) (hs : d.source = sphereSignedCollarSource)
  (hI : d.target ⊆ W.interior)
  (heq : ∀ z s, d (z, s) = E.boundedSplitTubeMap h hlin (z.down, s))
  (hc : E.toTorus.components.count = 2) (hn : E.toTorus.pairing.count = 1)
  {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
  (havρ : ∀ r, Disjoint ((E.toTorus.external.shrink hρ hρ1).collar r).target d.target)

local notation "B₀" => E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ
local notation "Bᵢ" i => E.plugSideBoundary h hlin d hs hI heq hc hn hρ hρ1 havρ i
local notation "Kᵢ" i => E.plugSideCapping h hlin d hs hI heq hc hn hρ hρ1 havρ i
local notation "Pᵢ" i => E.plugComponentCapBallChart h hlin d hs hI heq hc hn hρ hρ1 havρ i

theorem exists_plugComponentCapCollarGerm :
    ∃ η > (0 : ℝ), η ≤ 1 / 4 ∧
      ∀ (i : Fin 2) (z : ClosureSphere.{u}) (r : ℝ) (hr : 1 ≤ r), r < 1 + η →
        (Pᵢ i).chart (r • z.down.val) =
          (Kᵢ i).core ((Bᵢ i).sphere 0
            ((Kᵢ i).attaching 0 z, halfPoint (2 * r - 2) (by linarith))) := by
  obtain ⟨η, hη, hη1, hg⟩ := exists_boundedPlugSideBallMap_normal_germ d hs hI
    (E.toTorus.external.shrink hρ hρ1)
    (E.toTorus.external_exhausted.trans (E.toTorus.external.shrink_image hρ hρ1).symm)
    havρ E h hlin heq
  refine ⟨η, hη, hη1.le, ?_⟩
  intro i z r hr hrη
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hr1 : r ≤ 5 / 4 := by linarith
  have hnorm : ‖r • z.down.val‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0,
      mem_sphere_zero_iff_norm.mp z.down.property, mul_one]
  have hsrc : r • z.down.val ∈ Metric.ball 0 (5 / 2) := by
    apply mem_ball_zero_iff.mpr
    rw [hnorm]
    linarith
  have hnear : |‖(B₀).capBallAmbientExtension i (r • z.down.val)‖ - 1| < η := by
    erw [(B₀).capBallAmbientExtension_norm, hnorm, abs_of_nonneg (by linarith)]
    linarith
  have hhalf : ((Kᵢ i).attaching 0 z, halfPoint (2 * r - 2) (by linarith)) ∈
      sphereHalfCollarSource := by
    change 2 * r - 2 < 1
    linarith
  apply Subtype.ext
  change (E.plugComponentCapChart h hlin d hs hI heq hc hn hρ hρ1 havρ i
    (r • z.down.val)).val = _
  erw [E.plugComponentCapChart_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i _ hsrc]
  erw [boundedPlugCapBallChart_apply, boundedPlugCapBallMap, hg i _ hnear,
    capExtension_polar (B₀) i z hr0, (B₀).boundedPlugCapNormal_positive i _ hr hr1]
  erw [E.plugSideCapping_core, E.plugSideBoundary_sphere_apply
    h hlin d hs hI heq hc hn hρ hρ1 havρ i _ hhalf, E.plugSideCapping_attaching]

theorem plugComponentCapCollarGerm_zero (i : Fin 2) (z : ClosureSphere.{u}) :
    (Pᵢ i).chart z.down.val = (Kᵢ i).core ((Bᵢ i).sphereMap 0 ((Kᵢ i).attaching 0 z)) := by
  obtain ⟨η, hη, hη1, hg⟩ := E.exists_plugComponentCapCollarGerm
    h hlin d hs hI heq hc hn hρ hρ1 havρ
  have hz := hg i z 1 le_rfl (by linarith)
  change (Pᵢ i).chart z.down.val =
    (Kᵢ i).core ((Bᵢ i).sphere 0 ((Kᵢ i).attaching 0 z, halfZero))
  convert hz using 1 <;> simp only [one_smul, mul_one, sub_self, halfZero]

end GC.Seifert.ElementaryPresentation
