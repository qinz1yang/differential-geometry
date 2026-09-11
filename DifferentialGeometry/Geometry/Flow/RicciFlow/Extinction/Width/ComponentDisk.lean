import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.Plateau
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype


noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

section SmoothExtension
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

theorem smoothDisk_subtypeVal_iff (U : TopologicalSpace.Opens Q) (v : C(Disk, U)) :
    letI : IsManifold I ∞ U := { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
    (∃ u : SmoothDisk (I := I) (Q := U), u.map = v) ↔
      ∃ u : SmoothDisk (I := I) (Q := Q), ∀ z, u.map z = (v z : Q) := by
  classical
  let : IsManifold I ∞ U := { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
  constructor
  · rintro ⟨u, hu⟩
    let w : C(Disk, Q) := ⟨fun z => (v z : Q), continuous_subtype_val.comp v.continuous⟩
    have hwsmooth : ∀ z : Disk, Nonempty (DiskLocalExtension (I := I) w z) := by
      intro z
      obtain ⟨F⟩ := u.smooth z
      refine ⟨{
        map := Subtype.val ∘ F.map
        domain := F.domain
        isOpen_domain := F.isOpen_domain
        mem_domain := F.mem_domain
        smooth := (contMDiff_subtype_val (I := I) (U := U)).comp_contMDiffOn F.smooth
        agrees := ?_ }⟩
      intro y hy
      have hh := congrArg (fun z : U => (z : Q)) (F.agrees hy)
      change (F.map y : Q) = diskExtension (Q := Q) (fun z => (v z : Q)) y
      simpa only [hu, diskExtension, dif_pos hy.2] using hh
    exact ⟨⟨w, hwsmooth⟩, fun _ => rfl⟩
  · rintro ⟨u, hu⟩
    have hvsmooth : ∀ z : Disk, Nonempty (DiskLocalExtension (I := I) v z) := by
      intro z
      obtain ⟨F⟩ := u.smooth z
      let S := F.domain ∩ F.map ⁻¹' (U : Set Q)
      have hS : IsOpen S := F.smooth.continuousOn.isOpen_inter_preimage F.isOpen_domain U.isOpen
      have hFz : F.map z = (v z : Q) := by
        calc
          F.map z = diskExtension u.map z := F.agrees ⟨F.mem_domain, z.property⟩
          _ = u.map z := diskExtension_coe u.map z
          _ = (v z : Q) := hu z
      have hzS : (z : ℂ) ∈ S := ⟨F.mem_domain, by
        change F.map (z : ℂ) ∈ U
        rw [hFz]
        exact (v z).property⟩
      let F0 : ℂ → U := fun y => if h : F.map y ∈ U then ⟨F.map y, h⟩ else v diskCenter
      have hF0 : EqOn (Subtype.val ∘ F0) F.map S := by
        intro y hy
        have hyU : F.map y ∈ U := hy.2
        simp only [Function.comp_apply, F0, dif_pos hyU]
      have hF0smooth : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ F0 S := by
        have hcompose : ContMDiffOn 𝓘(ℝ, ℂ) I ∞ (Subtype.val ∘ F0) S :=
          (F.smooth.mono inter_subset_left).congr hF0
        intro y hy
        exact (ContMDiffWithinAt.subtypeVal_comp_iff U F0 S y).mp (hcompose y hy)
      refine ⟨{
        map := F0
        domain := S
        isOpen_domain := hS
        mem_domain := hzS
        smooth := hF0smooth
        agrees := ?_ }⟩
      intro y hy
      apply Subtype.ext
      have hFy := F.agrees ⟨hy.1.1, hy.2⟩
      have hFy' : F.map y = u.map (⟨y, hy.2⟩ : Disk) := by
        simpa only [diskExtension, dif_pos hy.2] using hFy
      have huv := hu (⟨y, hy.2⟩ : Disk)
      change (F0 y : Q) = ((diskExtension (Q := U) v y : U) : Q)
      have hF0y : (F0 y : Q) = F.map y := hF0 hy.1
      rw [hF0y]
      simpa only [diskExtension, dif_pos hy.2] using hFy'.trans huv
    exact ⟨⟨v, hvsmooth⟩, rfl⟩

end SmoothExtension

section Area
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [T2Space Q]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] [T2Space Q] in
theorem mdifferentiableWithinAt_subtypeVal_iff (U : TopologicalSpace.Opens Q)
    (u : ℂ → U) (s : Set ℂ) (z : ℂ) :
    MDifferentiableWithinAt 𝓘(ℝ, ℂ) I (Subtype.val ∘ u) s z ↔
      MDifferentiableWithinAt 𝓘(ℝ, ℂ) I u s z :=
  ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] [T2Space Q] in
theorem mfderivWithin_subtypeVal (U : TopologicalSpace.Opens Q)
    (u : ℂ → U) (s : Set ℂ) (z : ℂ)
    (hu : MDifferentiableWithinAt 𝓘(ℝ, ℂ) I u s z)
    (hs : UniqueMDiffWithinAt 𝓘(ℝ, ℂ) s z) :
    mfderivWithin 𝓘(ℝ, ℂ) I (Subtype.val ∘ u) s z =
      mfderivWithin 𝓘(ℝ, ℂ) I u s z := by
  have h := mfderiv_comp_mfderivWithin z
    (hasMFDerivAt_subtype_val (I := I) U (u z)).mdifferentiableAt hu hs
  rw [mfderiv_subtype_val] at h
  exact h.trans (by ext v; rfl)

theorem parametricJacobian_subtypeVal (g : SmoothRiemannianMetric I Q)
    (U : TopologicalSpace.Opens Q) (u : ℂ → U) (s : Set ℂ) (z : ℂ)
    (hs : UniqueMDiffWithinAt 𝓘(ℝ, ℂ) s z) :
    letI : IsManifold I ∞ U := { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
    parametricJacobian (g.restrictOpen U) u s z =
      parametricJacobian g (Subtype.val ∘ u) s z := by
  let : IsManifold I ∞ U := { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
  by_cases hu : MDifferentiableWithinAt 𝓘(ℝ, ℂ) I u s z
  · have hv := (mdifferentiableWithinAt_subtypeVal_iff U u s z).mpr hu
    have hd := mfderivWithin_subtypeVal U u s z hu hs
    simp only [parametricJacobian, if_pos hu, if_pos hv]
    rw [hd]
    rfl
  · have hv : ¬ MDifferentiableWithinAt 𝓘(ℝ, ℂ) I (Subtype.val ∘ u) s z :=
      fun h => hu ((mdifferentiableWithinAt_subtypeVal_iff U u s z).mp h)
    simp only [parametricJacobian, if_neg hu, if_neg hv]

omit [T2Space Q] in
theorem diskExtension_subtypeVal (U : TopologicalSpace.Opens Q) (u : Disk → U) :
    diskExtension (fun z => (u z : Q)) = Subtype.val ∘ diskExtension u := by
  funext z
  simp only [diskExtension, Function.comp_apply]
  split_ifs <;> rfl

theorem diskArea_subtypeVal (g : SmoothRiemannianMetric I Q)
    (U : TopologicalSpace.Opens Q) (u : C(Disk, U)) :
    letI : IsManifold I ∞ U := { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
    diskArea (g.restrictOpen U) u = diskArea g (fun z => (u z : Q)) := by
  let : IsManifold I ∞ U := { U.instHasGroupoid (contDiffGroupoid ∞ I) with }
  unfold diskArea
  apply setIntegral_congr_fun Metric.isClosed_closedBall.measurableSet
  intro z hz
  simp only [diskJacobian, diskExtension_subtypeVal]
  exact parametricJacobian_subtypeVal g U (diskExtension u) _ z
    (disk_uniqueDiffWithinAt (⟨z, hz⟩ : Disk)).uniqueMDiffWithinAt

end Area

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
