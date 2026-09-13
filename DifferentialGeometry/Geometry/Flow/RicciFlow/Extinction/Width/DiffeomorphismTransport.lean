import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiskBoundaryIntegral
import DifferentialGeometry.Topology.StandardModel
import DifferentialGeometry.Geometry.Curvature.RicciPullback
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.Pullback
import DifferentialGeometry.Geometry.Comparison.Variation.EndpointParallel

noncomputable section
open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

namespace DifferentialGeometry
namespace Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] [IsManifold 𝓘(ℝ, E) ∞ A] in
theorem mfderiv_symm_apply_mfderiv_apply (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A)
    (p : Q) (X : TangentSpace I p) :
    mfderiv 𝓘(ℝ, E) I (Φ.symm : A → Q) (Φ p)
      (mfderiv I 𝓘(ℝ, E) (Φ : Q → A) p X) = X := by
  have h1 : MDifferentiableAt I 𝓘(ℝ, E) (Φ : Q → A) p :=
    Φ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt 𝓘(ℝ, E) I (Φ.symm : A → Q) (Φ p) :=
    Φ.symm.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hid : (fun y => Φ.symm (Φ y)) = id := funext fun y => Φ.symm_apply_apply y
  have hcomp := mfderiv_comp (I := I) (I' := 𝓘(ℝ, E)) (I'' := I)
    (f := (Φ : Q → A)) (g := (Φ.symm : A → Q)) p h2 h1
  simp only [Function.comp_def] at hcomp
  rw [hid, mfderiv_id] at hcomp
  exact (congrArg (fun (L : TangentSpace I p →L[ℝ] TangentSpace I p) => L X) hcomp).symm

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] [IsManifold 𝓘(ℝ, E) ∞ A] in
theorem mfderiv_apply_mfderiv_symm_apply (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A)
    (y : A) (X : TangentSpace 𝓘(ℝ, E) y) :
    mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (Φ.symm y)
      (mfderiv 𝓘(ℝ, E) I (Φ.symm : A → Q) y X) = X := by
  have h1 : MDifferentiableAt 𝓘(ℝ, E) I (Φ.symm : A → Q) y :=
    Φ.symm.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt I 𝓘(ℝ, E) (Φ : Q → A) (Φ.symm y) :=
    Φ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hid : (fun z => Φ (Φ.symm z)) = id := funext fun z => Φ.apply_symm_apply z
  have hcomp := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, E))
    (f := (Φ.symm : A → Q)) (g := (Φ : Q → A)) y h2 h1
  simp only [Function.comp_def] at hcomp
  rw [hid, mfderiv_id] at hcomp
  exact (congrArg (fun (L : TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) y) => L X)
    hcomp).symm

theorem inner_pullbackMetricCross_comp [T2Space Q] [T2Space A]
    (g : SmoothRiemannianMetric I Q) (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (p : Q)
    (v w : TangentSpace I p) :
    (Diffeomorph.pullbackMetricCross g Φ.symm).inner (Φ p)
        (mfderiv I 𝓘(ℝ, E) (Φ : Q → A) p v)
        (mfderiv I 𝓘(ℝ, E) (Φ : Q → A) p w) = g.inner p v w := by
  rw [Diffeomorph.pullbackMetricCross_inner]
  simp only [mfderiv_symm_apply_mfderiv_apply]
  rw [Φ.symm_apply_apply]

end Diffeomorph
end DifferentialGeometry
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A]

namespace CurveMap

def postcomposeDiffeomorph (c : CurveMap Q) (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) : CurveMap A :=
  fun θ t => Φ (c θ t)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] [IsManifold 𝓘(ℝ, E) ∞ A] in
theorem lift_postcomposeDiffeomorph (c : CurveMap Q) (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (x t : ℝ) :
    (c.postcomposeDiffeomorph Φ).lift x t = Φ (c.lift x t) := rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] [IsManifold 𝓘(ℝ, E) ∞ A] in
theorem X_postcomposeDiffeomorph (c : CurveMap Q) (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A)
    (x t : ℝ) (hf : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y => c.lift y t) x) :
    (c.postcomposeDiffeomorph Φ).X x t =
      mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (c.lift x t) (c.X x t) := by
  have hΦ : MDifferentiableAt I 𝓘(ℝ, E) (Φ : Q → A) (c.lift x t) :=
    Φ.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  rw [CurveMap.X, CurveMap.X]
  rw [show (fun y => (c.postcomposeDiffeomorph Φ).lift y t) =
      (Φ : Q → A) ∘ (fun y => c.lift y t) from rfl]
  rw [mfderiv_comp x hΦ hf]
  rfl

theorem speed_postcomposeDiffeomorph [T2Space Q] [T2Space A] (c : CurveMap Q)
    (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (g : ℝ → SmoothRiemannianMetric I Q) (x t : ℝ)
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y => c.lift y t) x) :
    (c.postcomposeDiffeomorph Φ).speed (fun s => Diffeomorph.pullbackMetricCross (g s) Φ.symm) x t =
      c.speed g x t := by
  have hinner : (Diffeomorph.pullbackMetricCross (g t) Φ.symm).inner (Φ (c.lift x t))
      (mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (c.lift x t) (c.X x t))
      (mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (c.lift x t) (c.X x t)) =
      (g t).inner (c.lift x t) (c.X x t) (c.X x t) :=
    Diffeomorph.inner_pullbackMetricCross_comp (g t) Φ (c.lift x t) (c.X x t) (c.X x t)
  rw [CurveMap.speed, CurveMap.speed, CurveMap.lift_postcomposeDiffeomorph,
    CurveMap.X_postcomposeDiffeomorph c Φ x t hf, hinner]
theorem unitTangent_postcomposeDiffeomorph [T2Space Q] [T2Space A] (c : CurveMap Q)
    (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (g : ℝ → SmoothRiemannianMetric I Q) (x t : ℝ)
    (hf : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y => c.lift y t) x) :
    (c.postcomposeDiffeomorph Φ).unitTangent
        (fun s => Diffeomorph.pullbackMetricCross (g s) Φ.symm) x t =
      mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (c.lift x t) (c.unitTangent g x t) := by
  rw [CurveMap.unitTangent, CurveMap.unitTangent,
    CurveMap.speed_postcomposeDiffeomorph c Φ g x t hf,
    CurveMap.X_postcomposeDiffeomorph c Φ x t hf, map_smul]
  rfl

theorem covDerivAlong_comp_symm [I.Boundaryless] [T2Space Q] [T2Space A]
    (g : SmoothRiemannianMetric I Q) (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A)
    (γ : ℝ → Q) (V : ∀ s, TangentSpace I (γ s)) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ t)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) :
    covDerivAlong (Diffeomorph.pullbackMetricCross g Φ.symm) (fun s => Φ (γ s))
        (fun s => mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (γ s) (V s)) t =
      mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (γ t) (covDerivAlong g γ V t) := by
  have hγ' : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun s => Φ (γ s)) t :=
    Φ.contMDiff.contMDiffAt.comp t hγ
  have hV' : DifferentiableAt ℝ
      (chartRepAt (I := 𝓘(ℝ, E)) (fun s => Φ (γ s))
        (fun s => mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (γ s) (V s)) t) t :=
    chartRep_map_diff (I := I) (J := 𝓘(ℝ, E)) Φ γ V t
      (hγ.mdifferentiableAt (by simp)) hV
  have hnat := covAlong_natCrossAt (I := 𝓘(ℝ, E)) (J := I) g Φ.symm
    (fun s => Φ (γ s))
    (fun s => mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (γ s) (V s)) t hγ' hV'
  have h1 := congrArg
    (fun x => mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (Φ.symm (Φ (γ t))) x) hnat
  simp only [Diffeomorph.mfderiv_apply_mfderiv_symm_apply] at h1
  rw [show (fun s => Φ.symm (Φ (γ s))) = γ from
    funext fun s => Φ.symm_apply_apply (γ s)] at h1
  rw [show Φ.symm (Φ (γ t)) = γ t from Φ.symm_apply_apply (γ t)] at h1
  simpa only [Diffeomorph.mfderiv_symm_apply_mfderiv_apply] using h1

theorem Dx_postcomposeDiffeomorph [I.Boundaryless] [T2Space Q] [T2Space A]
    (c : CurveMap Q) (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (g : ℝ → SmoothRiemannianMetric I Q)
    (V : c.Field (I := I)) (x t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (fun y => c.lift y t) x)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) (fun y => c.lift y t)
      (fun y => V y t) x) x) :
    (c.postcomposeDiffeomorph Φ).Dx (fun s => Diffeomorph.pullbackMetricCross (g s) Φ.symm)
        (fun y t' => mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (c.lift y t') (V y t')) x t =
      mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (c.lift x t) (c.Dx g V x t) := by
  simp only [CurveMap.Dx]
  exact covDerivAlong_comp_symm (g t) Φ (fun y => c.lift y t) (fun y => V y t) x hγ hV

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] in
theorem slice_contMDiffAt (c : CurveMap Q) (J : Set ℝ) (hc : c.SmoothOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) (x : ℝ) :
    ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (fun y => c.lift y t) x :=
  (((contMDiffOn_univ.mp (CurveMap.space_slice_contMDiffOn c J hc t ht)) x).contMDiffAt
    Filter.univ_mem)

omit [FiniteDimensional ℝ E] in
theorem unitTangent_chartRep_differentiableAt [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)]
    (c : CurveMap Q) (g : ℝ → SmoothRiemannianMetric I Q) (t x : ℝ)
    (hc : c.SmoothOn (I := I) univ) (hi : c.ImmersedOn (I := I) univ) :
    DifferentiableAt ℝ (chartRepAt (I := I) (fun y => c.lift y t)
      (fun y => c.unitTangent g y t) x) x :=
  Variation.chartRepAt_differentiableAt_of_total_contMDiffAt
    ((c.unitTangent_contMDiff g univ hc hi t (mem_univ t)).contMDiffAt.of_le
      (by decide : (2 : WithTop ℕ∞) ≤ ∞))

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] in
theorem slice_mdifferentiableAt (c : CurveMap Q) (J : Set ℝ) (hc : c.SmoothOn (I := I) J)
    (t : ℝ) (ht : t ∈ J) (x : ℝ) :
    MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y => c.lift y t) x :=
  (CurveMap.slice_contMDiffAt c J hc t ht x).mdifferentiableAt (by simp)

theorem curvatureVector_postcomposeDiffeomorph [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [T2Space Q] [T2Space A]
    (c : CurveMap Q) (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (g : ℝ → SmoothRiemannianMetric I Q)
    (hc : c.SmoothOn (I := I) univ) (hi : c.ImmersedOn (I := I) univ) (x t : ℝ) :
    (c.postcomposeDiffeomorph Φ).curvatureVector
        (fun s => Diffeomorph.pullbackMetricCross (g s) Φ.symm) x t =
      mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (c.lift x t) (c.curvatureVector g x t) := by
  have hV : DifferentiableAt ℝ (chartRepAt (I := I) (fun y => c.lift y t)
      (fun y => c.unitTangent g y t) x) x :=
    CurveMap.unitTangent_chartRep_differentiableAt c g t x hc hi
  have hVT : (c.postcomposeDiffeomorph Φ).unitTangent
      (fun s => Diffeomorph.pullbackMetricCross (g s) Φ.symm) =
      fun y t' => mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (c.lift y t') (c.unitTangent g y t') := by
    funext y t'
    exact CurveMap.unitTangent_postcomposeDiffeomorph c Φ g y t'
      (CurveMap.slice_mdifferentiableAt c univ hc t' (mem_univ t') y)
  rw [CurveMap.curvatureVector, CurveMap.curvatureVector, CurveMap.Ds, CurveMap.Ds, hVT,
    CurveMap.Dx_postcomposeDiffeomorph c Φ g (c.unitTangent g) x t
      (CurveMap.slice_contMDiffAt c univ hc t (mem_univ t) x) hV,
    CurveMap.speed_postcomposeDiffeomorph c Φ g x t
      (CurveMap.slice_mdifferentiableAt c univ hc t (mem_univ t) x)]
  rw [map_smul]
  rfl

end CurveMap
end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] [IsManifold 𝓘(ℝ, E) ∞ A] in
theorem diskExtension_comp_diffeomorph (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A)
    (u : SmoothDisk (I := I) (Q := Q)) :
    diskExtension (SmoothDisk.comp_diffeomorph Φ u).map =
      fun z => Φ (diskExtension u.map z) := by
  funext z
  by_cases hz : z ∈ Metric.closedBall (0 : ℂ) 1
  · rw [diskExtension, dif_pos hz, diskExtension, dif_pos hz]
    rfl
  · rw [diskExtension, dif_neg hz, diskExtension, dif_neg hz]
    rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] [IsManifold 𝓘(ℝ, E) ∞ A] in
theorem SmoothDisk.differential_comp_diffeomorph (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A)
    (u : SmoothDisk (I := I) (Q := Q)) (z : Disk) (X : ℂ) :
    (SmoothDisk.comp_diffeomorph Φ u).differential z X =
      mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (u.map z) (u.differential z X) := by
  have hL : (SmoothDisk.comp_diffeomorph Φ u).differential z X =
      mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E)
        (diskExtension (SmoothDisk.comp_diffeomorph Φ u).map)
        (Metric.closedBall (0 : ℂ) 1) (z : ℂ) X := rfl
  have hR : u.differential z X =
      mfderivWithin 𝓘(ℝ, ℂ) I (diskExtension u.map)
        (Metric.closedBall (0 : ℂ) 1) (z : ℂ) X := rfl
  rw [hL, hR, diskExtension_comp_diffeomorph]
  have hcomp := mfderiv_comp_mfderivWithin_of_eq (s := Metric.closedBall (0 : ℂ) 1)
    (f := diskExtension u.map) (g := (Φ : Q → A)) (y := u.map z)
    (Φ.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    ((u.contMDiffOn_extension (z : ℂ) z.property).mdifferentiableWithinAt (by simp))
    (disk_uniqueDiffWithinAt z).uniqueMDiffWithinAt
    (diskExtension_coe u.map z)
  simp only [Function.comp_def] at hcomp ⊢
  rw [hcomp]
  rfl


theorem SmoothDisk.inner_pullback_comp_diffeomorph [T2Space A]
    (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (g : SmoothRiemannianMetric I Q) (p : Q)
    (v w : TangentSpace I p) :
    (Diffeomorph.pullbackMetricCross g Φ.symm).inner (Φ p)
        (mfderiv I 𝓘(ℝ, E) (Φ : Q → A) p v)
        (mfderiv I 𝓘(ℝ, E) (Φ : Q → A) p w) = g.inner p v w := by
  rw [Diffeomorph.pullbackMetricCross_inner]
  simp only [Diffeomorph.mfderiv_symm_apply_mfderiv_apply]
  rw [Φ.symm_apply_apply]

theorem SmoothDisk.inner_comp_diffeomorph [T2Space A]
    (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (g : SmoothRiemannianMetric I Q)
    (u : SmoothDisk (I := I) (Q := Q)) (z : Disk) (X Y : ℂ) :
    (Diffeomorph.pullbackMetricCross g Φ.symm).inner
        ((SmoothDisk.comp_diffeomorph Φ u).map z)
        ((SmoothDisk.comp_diffeomorph Φ u).differential z X)
        ((SmoothDisk.comp_diffeomorph Φ u).differential z Y) =
      g.inner (u.map z) (u.differential z X) (u.differential z Y) := by
  rw [SmoothDisk.comp_diffeomorph_map]
  rw [SmoothDisk.differential_comp_diffeomorph, SmoothDisk.differential_comp_diffeomorph]
  exact SmoothDisk.inner_pullback_comp_diffeomorph Φ g (u.map z)
    (u.differential z X) (u.differential z Y)

theorem SmoothDisk.conformalFactor_comp_diffeomorph [T2Space A]
    (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (g : SmoothRiemannianMetric I Q)
    (u : SmoothDisk (I := I) (Q := Q)) (z : Disk) :
    (SmoothDisk.comp_diffeomorph Φ u).conformalFactor
        (Diffeomorph.pullbackMetricCross g Φ.symm) z = u.conformalFactor g z := by
  rw [SmoothDisk.conformalFactor, SmoothDisk.conformalFactor, SmoothDisk.inner_comp_diffeomorph]

theorem SmoothDisk.isConformal_comp_diffeomorph [T2Space A]
    (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (g : SmoothRiemannianMetric I Q)
    (u : SmoothDisk (I := I) (Q := Q)) (h : u.IsConformal g) :
    (SmoothDisk.comp_diffeomorph Φ u).IsConformal
      (Diffeomorph.pullbackMetricCross g Φ.symm) := by
  intro z
  obtain ⟨h1, h2⟩ := h z
  exact ⟨(SmoothDisk.inner_comp_diffeomorph Φ g u z 1 Complex.I).trans h1,
    (SmoothDisk.inner_comp_diffeomorph Φ g u z 1 1).trans
      (h2.trans (SmoothDisk.inner_comp_diffeomorph Φ g u z Complex.I Complex.I).symm)⟩

theorem sectionalCurvature_pullbackMetricCross [I.Boundaryless] [T2Space Q] [T2Space A]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) A) (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A)
    (x : Q) (v w : TangentSpace I x) :
    sectionalCurvature (I := I) (Diffeomorph.pullbackMetricCross g Φ) x v w =
      sectionalCurvature (I := 𝓘(ℝ, E)) g (Φ x)
        (mfderiv I 𝓘(ℝ, E) (Φ : Q → A) x v)
        (mfderiv I 𝓘(ℝ, E) (Φ : Q → A) x w) := by
  rw [Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div,
    Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div]
  rw [DifferentialGeometry.Geometry.Curvature.metricRm04Standard_pullbackCross]
  simp only [Diffeomorph.pullbackMetricCross_inner]


theorem sectionalCurvature_pullbackMetricCross_comp [I.Boundaryless] [T2Space Q] [T2Space A]
    (g : SmoothRiemannianMetric I Q) (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A)
    (x : Q) (v w : TangentSpace I x) :
    sectionalCurvature (I := 𝓘(ℝ, E)) (Diffeomorph.pullbackMetricCross g Φ.symm) (Φ x)
        (mfderiv I 𝓘(ℝ, E) (Φ : Q → A) x v)
        (mfderiv I 𝓘(ℝ, E) (Φ : Q → A) x w) = sectionalCurvature (I := I) g x v w := by
  rw [Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div,
    Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div]
  rw [DifferentialGeometry.Geometry.Curvature.metricRm04Standard_pullbackCross
    (g := g) (Phi := Φ.symm) (x := Φ x)
    (X := mfderiv I 𝓘(ℝ, E) (Φ : Q → A) x v)
    (Y := mfderiv I 𝓘(ℝ, E) (Φ : Q → A) x w)
    (Z := mfderiv I 𝓘(ℝ, E) (Φ : Q → A) x w)
    (W := mfderiv I 𝓘(ℝ, E) (Φ : Q → A) x v)]
  simp only [Diffeomorph.pullbackMetricCross_inner, Diffeomorph.mfderiv_symm_apply_mfderiv_apply]
  rw [Φ.symm_apply_apply]

theorem SmoothDisk.sectionalDensity_comp_diffeomorph [I.Boundaryless] [T2Space Q] [T2Space A]
    (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (g : SmoothRiemannianMetric I Q)
    (u : SmoothDisk (I := I) (Q := Q)) (z : Disk) :
    (SmoothDisk.comp_diffeomorph Φ u).sectionalDensity
        (Diffeomorph.pullbackMetricCross g Φ.symm) z = u.sectionalDensity g z := by
  rw [SmoothDisk.sectionalDensity, SmoothDisk.sectionalDensity,
    SmoothDisk.conformalFactor_comp_diffeomorph]
  by_cases hpos : 0 < u.conformalFactor g z
  · rw [if_pos hpos, if_pos hpos]
    congr 1
    rw [SmoothDisk.differential_comp_diffeomorph, SmoothDisk.differential_comp_diffeomorph]
    exact sectionalCurvature_pullbackMetricCross_comp g Φ (u.map z)
      (u.differential z 1) (u.differential z Complex.I)
  · rw [if_neg hpos, if_neg hpos]


theorem SmoothDisk.inwardConormal_comp_diffeomorph [T2Space Q] [T2Space A]
    (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (g : SmoothRiemannianMetric I Q)
    (u : SmoothDisk (I := I) (Q := Q)) (z : Disk) :
    (SmoothDisk.comp_diffeomorph Φ u).inwardConormal
        (Diffeomorph.pullbackMetricCross g Φ.symm) z =
      mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (u.map z) (u.inwardConormal g z) := by
  have hcf := SmoothDisk.conformalFactor_comp_diffeomorph Φ g u z
  rw [SmoothDisk.inwardConormal, SmoothDisk.inwardConormal, SmoothDisk.comp_diffeomorph_map, hcf]
  by_cases h : 0 < u.conformalFactor g z
  · rw [if_pos h, if_pos h, SmoothDisk.differential_comp_diffeomorph, map_smul]
  · rw [if_neg h, if_neg h, map_zero]

theorem SmoothDisk.boundarySpeed_comp_diffeomorph [T2Space Q] [T2Space A]
    (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (g : SmoothRiemannianMetric I Q)
    (u : SmoothDisk (I := I) (Q := Q)) (x : ℝ) :
    (SmoothDisk.comp_diffeomorph Φ u).boundarySpeed
        (Diffeomorph.pullbackMetricCross g Φ.symm) x = u.boundarySpeed g x := by
  rw [SmoothDisk.boundarySpeed, SmoothDisk.boundarySpeed, SmoothDisk.comp_diffeomorph_map,
    SmoothDisk.differential_comp_diffeomorph, Diffeomorph.inner_pullbackMetricCross_comp]

theorem disk_curvature_inequality_of_standardModelCopy
    [hBoundary : I.Boundaryless] [hT2 : T2Space Q]
    (g : SmoothRiemannianMetric I Q) (hdim : Module.finrank ℝ E = 3)
    (u : SmoothDisk (I := I) (Q := Q))
    (γ : RegularLoop I Q) (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = γ (sigma.map theta))
    (c : Geometry.Topology.StandardModelCopy I Q E) [CompactSpace c.Q]
    (γ' : RegularLoop 𝓘(ℝ, E) c.Q)
    (hγ' : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (loopLift γ'.toContinuousLoop))
    (himm' : ∀ x, loopVelocity (I := 𝓘(ℝ, E)) γ'.toContinuousLoop x ≠ 0)
    (htrace' : ∀ theta, (SmoothDisk.comp_diffeomorph c.equiv u).map (diskBoundary theta) =
      γ' (sigma.map theta))
    (hnonconstant' : ¬ ∃ q : c.Q, ∀ z : Disk, (SmoothDisk.comp_diffeomorph c.equiv u).map z = q)
    (hconformal' : (SmoothDisk.comp_diffeomorph c.equiv u).IsConformal
      (Diffeomorph.pullbackMetricCross g c.equiv.symm))
    (hharmonic' : (SmoothDisk.comp_diffeomorph c.equiv u).IsHarmonic
      (Diffeomorph.pullbackMetricCross g c.equiv.symm))
    (hbd : ∀ x : ℝ, (SmoothDisk.comp_diffeomorph c.equiv u).boundaryCurvatureDensity
        (Diffeomorph.pullbackMetricCross g c.equiv.symm) γ' sigma htrace' x =
      u.boundaryCurvatureDensity g γ sigma htrace x) :
    IntegrableOn (diskExtension (u.sectionalDensity g)) (Metric.closedBall (0 : ℂ) 1) ∧
      IntervalIntegrable (u.boundaryCurvatureDensity g γ sigma htrace) volume 0 1 ∧
      2 * Real.pi ≤
        (∫ z in Metric.closedBall (0 : ℂ) 1, diskExtension (u.sectionalDensity g) z) +
        ∫ x in (0 : ℝ)..1, u.boundaryCurvatureDensity g γ sigma htrace x := by
  let _ := hdim
  let g' : SmoothRiemannianMetric 𝓘(ℝ, E) c.Q := Diffeomorph.pullbackMetricCross g c.equiv.symm
  let u' : SmoothDisk (I := 𝓘(ℝ, E)) (Q := c.Q) := SmoothDisk.comp_diffeomorph c.equiv u
  obtain ⟨hint1, hint2, hineq⟩ := SmoothDisk.curvature_inequality_standardModel g' u'
    hnonconstant' hconformal' hharmonic' γ' hγ' himm' sigma htrace'
  have hsd : diskExtension (u'.sectionalDensity g') = diskExtension (u.sectionalDensity g) := by
    funext z
    by_cases hz : z ∈ Metric.closedBall (0 : ℂ) 1
    · rw [diskExtension, dif_pos hz, diskExtension, dif_pos hz]
      exact SmoothDisk.sectionalDensity_comp_diffeomorph c.equiv g u ⟨z, hz⟩
    · rw [diskExtension, dif_neg hz, diskExtension, dif_neg hz]
      exact SmoothDisk.sectionalDensity_comp_diffeomorph c.equiv g u diskCenter
  refine ⟨?_, ?_, ?_⟩
  · rw [← hsd]
    exact hint1
  · exact hint2.congr (fun x _ => hbd x)
  · rw [hsd] at hineq
    rw [intervalIntegral.integral_congr (fun x _ => hbd x)] at hineq
    exact hineq

omit [FiniteDimensional ℝ E] in
theorem chartRepAt_velocityField_differentiableAt {γ : ℝ → Q} {t : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ t) :
    DifferentiableAt ℝ (chartRepAt (I := I) γ
      (fun s => mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)) t) t := by
  refine Variation.chartRepAt_differentiableAt_of_total_contMDiffAt
    (I := I) (V := fun s => mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)) ?_
  exact hγ.velocityLift (m := 2) (by decide)

omit [FiniteDimensional ℝ E] in
theorem mfderiv_straightLine_apply_one (z v : ℂ) (s : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (fun t : ℝ => z + t • v) s (1 : ℝ) = v := by
  have h : HasFDerivAt (fun t : ℝ => z + t • v) ((1 : ℝ →L[ℝ] ℝ).smulRight v) s :=
    ((hasFDerivAt_id (x := s)).smul_const v).const_add z
  rw [mfderiv_eq_fderiv, h.fderiv]
  change ((1 : ℝ →L[ℝ] ℝ) (1 : ℝ)) • v = v
  simp

omit [FiniteDimensional ℝ E] in
theorem contMDiffAt_straightLine (z v : ℂ) (s : ℝ) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ (fun t : ℝ => z + t • v) s :=
  (by fun_prop : ContDiffAt ℝ ∞ (fun t : ℝ => z + t • v) s).contMDiffAt

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] in
theorem mfderiv_comp_straightLine {F : ℂ → Q} {z v : ℂ} {s : ℝ}
    (hF : MDifferentiableAt 𝓘(ℝ, ℂ) I F (z + s • v)) :
    mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ => F (z + t • v)) s (1 : ℝ) =
      mfderiv 𝓘(ℝ, ℂ) I F (z + s • v) v := by
  have h1 := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℂ)) (I'' := I)
    (f := fun t : ℝ => z + t • v) (g := F) (x := s) hF
    ((contMDiffAt_straightLine z v s).mdifferentiableAt (by decide))
    (1 : TangentSpace 𝓘(ℝ, ℝ) s)
  have hlin : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (fun t : ℝ => z + t • v) s)
      (1 : TangentSpace 𝓘(ℝ, ℝ) s) = v :=
    mfderiv_straightLine_apply_one z v s
  rw [hlin, Function.comp_def] at h1
  exact h1

omit [FiniteDimensional ℝ E] in
theorem chartRepAt_straightLine_differentiableAt {F : ℂ → Q} {z v : ℂ}
    (hF : ContMDiffAt 𝓘(ℝ, ℂ) I ∞ F z) :
    DifferentiableAt ℝ (chartRepAt (I := I) (fun t : ℝ => F (z + t • v))
      (fun t : ℝ => mfderiv 𝓘(ℝ, ℂ) I F (z + t • v) v) 0) 0 := by
  have hnear : ∀ᶠ y in 𝓝 z, MDifferentiableAt 𝓘(ℝ, ℂ) I F y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (I := 𝓘(ℝ, ℂ)) (I' := I) (f := F) (n := 2)
      (by decide)).mp (hF.of_le (by decide))).mono
      (fun y hy => hy.mdifferentiableAt (by decide))
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (fun t : ℝ => F (z + t • v)) 0 :=
    (show ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (F ∘ fun t : ℝ => z + t • v) 0 from
      hF.comp_of_eq (contMDiffAt_straightLine z v 0) (by simp))
  refine (chartRepAt_velocityField_differentiableAt (I := I) hγ).congr_of_eventuallyEq ?_
  have hline : Tendsto (fun t : ℝ => z + t • v) (𝓝 (0 : ℝ)) (𝓝 z) := by
    have hc : Continuous fun t : ℝ => z + t • v := by fun_prop
    simpa only [zero_smul, add_zero] using hc.tendsto (0 : ℝ)
  filter_upwards [hline.eventually hnear] with s hs
  simp only [chartRepAt_apply, mfderiv_comp_straightLine (I := I) hs]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] [IsManifold 𝓘(ℝ, E) ∞ A] in
theorem mfderiv_compDiffeomorph_straightLine [T2Space Q] [T2Space A]
    (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) {F : ℂ → Q} {z v : ℂ} {s : ℝ}
    (hF : MDifferentiableAt 𝓘(ℝ, ℂ) I F (z + s • v)) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w => Φ (F w)) (z + s • v) v =
      mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (F (z + s • v))
        (mfderiv 𝓘(ℝ, ℂ) I F (z + s • v) v) := by
  have hΦ : MDifferentiableAt I 𝓘(ℝ, E) (Φ : Q → A) (F (z + s • v)) :=
    Φ.contMDiff.contMDiffAt.mdifferentiableAt (by decide)
  simpa only [Function.comp_def] using
    (mfderiv_comp_apply (I := 𝓘(ℝ, ℂ)) (I' := I) (I'' := 𝓘(ℝ, E))
      (f := F) (g := (Φ : Q → A)) (x := z + s • v) hΦ hF v)

theorem covDerivAlong_straightLine_natCross [I.Boundaryless] [T2Space Q] [T2Space A]
    (g : SmoothRiemannianMetric I Q) (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A)
    {F : ℂ → Q} {z v : ℂ} (hF : ContMDiffAt 𝓘(ℝ, ℂ) I ∞ F z) :
    covDerivAlong (Diffeomorph.pullbackMetricCross g Φ.symm)
        (fun t : ℝ => Φ (F (z + t • v)))
        (fun t : ℝ => mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w => Φ (F w)) (z + t • v) v) 0 =
      mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (F (z + 0 • v))
        (covDerivAlong g (fun t : ℝ => F (z + t • v))
          (fun t : ℝ => mfderiv 𝓘(ℝ, ℂ) I F (z + t • v) v) 0) := by
  have hnear : ∀ᶠ y in 𝓝 z, MDifferentiableAt 𝓘(ℝ, ℂ) I F y := by
    have h2 : ContMDiffAt 𝓘(ℝ, ℂ) I 2 F z := hF.of_le (by decide)
    exact ((contMDiffAt_iff_contMDiffAt_nhds (I := 𝓘(ℝ, ℂ)) (I' := I) (f := F) (n := 2)
      (by decide)).mp h2).mono (fun y hy => hy.mdifferentiableAt (by decide))
  have hline : Tendsto (fun t : ℝ => z + t • v) (𝓝 (0 : ℝ)) (𝓝 z) := by
    have hc : Continuous fun t : ℝ => z + t • v := by fun_prop
    simpa only [zero_smul, add_zero] using hc.tendsto (0 : ℝ)
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (fun t : ℝ => F (z + t • v)) 0 := by
    have h := hF.comp_of_eq (contMDiffAt_straightLine z v 0) (by simp)
    simpa only [Function.comp_def] using h
  have hV : DifferentiableAt ℝ (chartRepAt (I := I) (fun t : ℝ => F (z + t • v))
      (fun t : ℝ => mfderiv 𝓘(ℝ, ℂ) I F (z + t • v) v) 0) 0 :=
    chartRepAt_straightLine_differentiableAt (I := I) hF
  have hnat := CurveMap.covDerivAlong_comp_symm (g := g) (Φ := Φ)
    (γ := fun t : ℝ => F (z + t • v))
    (V := fun t : ℝ => mfderiv 𝓘(ℝ, ℂ) I F (z + t • v) v) 0 hγ hV
  have hfield : (fun t : ℝ => (mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (F (z + t • v))
      (mfderiv 𝓘(ℝ, ℂ) I F (z + t • v) v) : E)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w => Φ (F w)) (z + t • v) v : E)) := by
    filter_upwards [hline.eventually hnear] with t ht
    exact congrArg (fun x => (x : E)) (mfderiv_compDiffeomorph_straightLine Φ ht).symm
  have hcongr := covDerivAlong_congr_germ (Diffeomorph.pullbackMetricCross g Φ.symm)
    (fun t : ℝ => Φ (F (z + t • v))) (fun t : ℝ => Φ (F (z + t • v)))
    (fun t : ℝ => mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (F (z + t • v))
      (mfderiv 𝓘(ℝ, ℂ) I F (z + t • v) v))
    (fun t : ℝ => mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w => Φ (F w)) (z + t • v) v)
    0 (by filter_upwards with t; rfl) hfield
  exact hcongr.symm.trans hnat

private noncomputable def straightLineTension (g : SmoothRiemannianMetric I Q)
    (F : ℂ → Q) (z v : ℂ) : TangentSpace I (F z) :=
  covDerivAlong g (fun t : ℝ => F (z + t • v))
    (fun t => mfderiv 𝓘(ℝ, ℂ) I F (z + t • v) v) 0

private noncomputable def diskLocalTensionRaw (g : SmoothRiemannianMetric I Q)
    (F : ℂ → Q) (z : ℂ) : TangentSpace I (F z) :=
  straightLineTension g F z (1 : ℂ) + straightLineTension g F z Complex.I

private theorem diskLocalTension_eq_raw (g : SmoothRiemannianMetric I Q) (F : ℂ → Q) (z : ℂ) :
    diskLocalTension g F z = diskLocalTensionRaw g F z := by
  simp only [diskLocalTension, diskLocalTensionRaw]
  generalize_proofs h1 h2
  apply congrArg₂ (fun x y : TangentSpace I (F z) => x + y)
  · cases h1
    rfl
  · cases h2
    rfl

private theorem straightLineTension_natCrossAt [I.Boundaryless] [T2Space Q] [T2Space A]
    (g : SmoothRiemannianMetric I Q) (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A)
    {F : ℂ → Q} {z : ℂ} (hF : ContMDiffAt 𝓘(ℝ, ℂ) I ∞ F z) (v : ℂ) :
    straightLineTension (Diffeomorph.pullbackMetricCross g Φ.symm) (fun w => Φ (F w)) z v =
      mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (F z) (straightLineTension g F z v) := by
  rw [straightLineTension, straightLineTension]
  rw [covDerivAlong_straightLine_natCross (g := g) (Φ := Φ) (v := v) hF]
  have key : ∀ X : TangentSpace I (F (z + (0 : ℝ) • v)),
      (mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (F (z + (0 : ℝ) • v)) X : E) =
        (mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (F z) X : E) := by
    intro X
    rw [show F (z + (0 : ℝ) • v) = F z from congrArg F (by simp)]
  exact key _

private theorem diskLocalTensionRaw_natCrossAt [I.Boundaryless] [T2Space Q] [T2Space A]
    (g : SmoothRiemannianMetric I Q) (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A)
    {F : ℂ → Q} {z : ℂ} (hF : ContMDiffAt 𝓘(ℝ, ℂ) I ∞ F z) :
    diskLocalTensionRaw (Diffeomorph.pullbackMetricCross g Φ.symm) (fun w => Φ (F w)) z =
      mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (F z) (diskLocalTensionRaw g F z) := by
  simp only [diskLocalTensionRaw]
  rw [map_add, straightLineTension_natCrossAt (g := g) (Φ := Φ) hF (1 : ℂ),
    straightLineTension_natCrossAt (g := g) (Φ := Φ) hF Complex.I]

theorem diskLocalTension_natCrossAt [I.Boundaryless] [T2Space Q] [T2Space A]
    (g : SmoothRiemannianMetric I Q) (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A)
    {F : ℂ → Q} {z : ℂ} (hF : ContMDiffAt 𝓘(ℝ, ℂ) I ∞ F z) :
    diskLocalTension (Diffeomorph.pullbackMetricCross g Φ.symm) (fun w => Φ (F w)) z =
      mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (F z) (diskLocalTension g F z) := by
  have h1 := diskLocalTension_eq_raw (Diffeomorph.pullbackMetricCross g Φ.symm)
    (fun w => Φ (F w)) z
  have h2 := diskLocalTension_eq_raw g F z
  have h3 := diskLocalTensionRaw_natCrossAt (g := g) (Φ := Φ) hF
  exact h1.trans (h3.trans (congrArg (mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (F z)) h2.symm))

theorem SmoothDisk.isHarmonic_comp_diffeomorph [I.Boundaryless] [T2Space Q] [T2Space A]
    (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (g : SmoothRiemannianMetric I Q)
    (u : SmoothDisk (I := I) (Q := Q)) (h : u.IsHarmonic g) :
    (SmoothDisk.comp_diffeomorph Φ u).IsHarmonic
      (Diffeomorph.pullbackMetricCross g Φ.symm) := by
  intro z F
  set G : ℂ → Q := fun w => Φ.symm (F.map w) with hG
  have hGsm : ContMDiffAt 𝓘(ℝ, ℂ) I ∞ G z :=
    (Φ.symm.contMDiff.comp_contMDiffOn F.smooth).contMDiffAt
      (F.isOpen_domain.mem_nhds F.mem_domain)
  have hnat := diskLocalTension_natCrossAt (g := g) (Φ := Φ) (F := G) hGsm
  have hfun : (fun w => Φ (G w)) = F.map := funext fun w => Φ.apply_symm_apply (F.map w)
  rw [hfun] at hnat
  have hagrees : EqOn G (diskExtension u.map) (F.domain ∩ Metric.closedBall (0 : ℂ) 1) := by
    intro w hw
    obtain ⟨hwd, hwb⟩ := hw
    have hFw : F.map w = Φ (u.map ⟨w, hwb⟩) := by
      have h1 : F.map w = diskExtension (SmoothDisk.comp_diffeomorph Φ u).map w :=
        F.agrees ⟨hwd, hwb⟩
      rw [h1, diskExtension, dif_pos hwb, SmoothDisk.comp_diffeomorph_map]
    change Φ.symm (F.map w) = diskExtension u.map w
    rw [hFw, Φ.symm_apply_apply]
    exact (diskExtension_coe u.map ⟨w, hwb⟩).symm
  have hzero : diskLocalTension g G z = 0 :=
    h z { map := G
          domain := F.domain
          isOpen_domain := F.isOpen_domain
          mem_domain := F.mem_domain
          smooth := Φ.symm.contMDiff.comp_contMDiffOn F.smooth
          agrees := hagrees }
  rw [hnat, hzero, map_zero]
  rfl

theorem SmoothDisk.boundaryCurvatureDensity_eq (u : SmoothDisk (I := I) (Q := Q))
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = γ (sigma.map theta)) (x : ℝ) :
    u.boundaryCurvatureDensity g γ sigma htrace x =
      (fun (v : TangentSpace I (u.map (diskBoundary (x : Surgery.Topology.Circle)))) =>
          g.inner (u.map (diskBoundary (x : Surgery.Topology.Circle))) v
              (u.inwardConormal g (diskBoundary (x : Surgery.Topology.Circle))) *
            u.boundarySpeed g x)
        (CurveMap.curvatureVector (fun theta _ => γ theta) (fun _ => g) (sigma.lift x) 0) := by
  simp only [SmoothDisk.boundaryCurvatureDensity]
  generalize_proofs h
  cases h
  rfl

def RegularLoop.postcomposeDiffeomorph (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (γ : RegularLoop I Q) :
    RegularLoop 𝓘(ℝ, E) A where
  toContinuousLoop :=
    ⟨fun θ => Φ (γ θ), Φ.contMDiff.continuous.comp γ.toContinuousLoop.continuous⟩
  contMDiff_lift := by
    change ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1
      (fun t : ℝ => Φ (γ.toContinuousLoop (t : Surgery.Topology.Circle)))
    exact ((Φ.contMDiff.of_le (by decide)).comp γ.contMDiff_lift)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] [IsManifold 𝓘(ℝ, E) ∞ A] in
@[simp] theorem RegularLoop.postcomposeDiffeomorph_apply (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A)
    (γ : RegularLoop I Q) (θ : Surgery.Topology.Circle) :
    γ.postcomposeDiffeomorph Φ θ = Φ (γ θ) := rfl

def boundaryDensityValue (g : SmoothRiemannianMetric I Q) (p : Q)
    (v n : TangentSpace I p) (s : ℝ) : ℝ :=
  g.inner p v n * s

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] in
theorem CurveMap.smoothOn_regularLoop (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop)) :
    CurveMap.SmoothOn (fun θ _ => γ θ) (I := I) univ := by
  rw [CurveMap.SmoothOn]
  intro p _
  have hfst : ContMDiffWithinAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) ∞
      (Prod.fst : ℝ × ℝ → ℝ) (univ ×ˢ univ) p := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffWithinAt_fst
  exact ((hγ p.1).contMDiffWithinAt).comp p hfst (fun q _ => mem_univ _)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] in
theorem CurveMap.immersedOn_regularLoop (γ : RegularLoop I Q)
    (himm : ∀ x, loopVelocity (I := I) γ.toContinuousLoop x ≠ 0) :
    CurveMap.ImmersedOn (fun θ _ => γ θ) (I := I) univ :=
  fun x _ _ => himm x

omit [FiniteDimensional ℝ E] in
theorem boundaryDensityValue_eq (g : SmoothRiemannianMetric I Q) (p : Q)
    (v n : TangentSpace I p) (s : ℝ) :
    boundaryDensityValue g p v n s = g.inner p v n * s := rfl

theorem SmoothDisk.boundaryCurvatureDensity_comp_diffeomorph [I.Boundaryless]
    [NeZero (Module.finrank ℝ E)] [T2Space Q] [T2Space A]
    (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (g : SmoothRiemannianMetric I Q)
    (u : SmoothDisk (I := I) (Q := Q)) (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop))
    (himm : ∀ x, loopVelocity (I := I) γ.toContinuousLoop x ≠ 0)
    (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = γ (sigma.map theta))
    (htrace' : ∀ theta, (SmoothDisk.comp_diffeomorph Φ u).map (diskBoundary theta) =
      (γ.postcomposeDiffeomorph Φ) (sigma.map theta)) (x : ℝ) :
    (SmoothDisk.comp_diffeomorph Φ u).boundaryCurvatureDensity
        (Diffeomorph.pullbackMetricCross g Φ.symm) (γ.postcomposeDiffeomorph Φ) sigma
        htrace' x =
      u.boundaryCurvatureDensity g γ sigma htrace x := by
  rw [SmoothDisk.boundaryCurvatureDensity_eq (u := SmoothDisk.comp_diffeomorph Φ u)
        (g := Diffeomorph.pullbackMetricCross g Φ.symm) (γ := γ.postcomposeDiffeomorph Φ)
        (sigma := sigma) (htrace := htrace') (x := x),
      SmoothDisk.boundaryCurvatureDensity_eq (u := u) (g := g) (γ := γ) (sigma := sigma)
        (htrace := htrace) (x := x)]
  simp only []
  have hW : CurveMap.curvatureVector (fun θ _ => (γ.postcomposeDiffeomorph Φ) θ)
        (fun _ => Diffeomorph.pullbackMetricCross g Φ.symm) (sigma.lift x) 0 =
      mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (u.map (diskBoundary (x : Surgery.Topology.Circle)))
        (CurveMap.curvatureVector (fun θ _ => γ θ) (fun _ => g) (sigma.lift x) 0) := by
    have hnat := CurveMap.curvatureVector_postcomposeDiffeomorph (fun θ _ => γ θ) Φ (fun _ => g)
      (CurveMap.smoothOn_regularLoop γ hγ)
      (CurveMap.immersedOn_regularLoop γ himm) (sigma.lift x) 0
    refine hnat.trans ?_
    have key : ∀ X : TangentSpace I (γ (sigma.lift x)),
        (mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (γ (sigma.lift x)) X : E) =
          (mfderiv I 𝓘(ℝ, E) (Φ : Q → A)
            (u.map (diskBoundary (x : Surgery.Topology.Circle))) X : E) := by
      intro X
      rw [show γ (sigma.lift x) = u.map (diskBoundary (x : Surgery.Topology.Circle)) from by
        rw [← sigma.lift_eq x]
        exact (htrace (x : Surgery.Topology.Circle)).symm]
    exact key _
  rw [hW, SmoothDisk.comp_diffeomorph_map, SmoothDisk.inwardConormal_comp_diffeomorph,
    SmoothDisk.boundarySpeed_comp_diffeomorph]
  rw [show (Diffeomorph.pullbackMetricCross g Φ.symm).inner
        (Φ (u.map (diskBoundary (x : Surgery.Topology.Circle))))
        (mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (u.map (diskBoundary (x : Surgery.Topology.Circle)))
          (CurveMap.curvatureVector (fun θ _ => γ θ) (fun _ => g) (sigma.lift x) 0))
        (mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (u.map (diskBoundary (x : Surgery.Topology.Circle)))
          (u.inwardConormal g (diskBoundary (x : Surgery.Topology.Circle)))) =
      g.inner (u.map (diskBoundary (x : Surgery.Topology.Circle)))
        (CurveMap.curvatureVector (fun θ _ => γ θ) (fun _ => g) (sigma.lift x) 0)
        (u.inwardConormal g (diskBoundary (x : Surgery.Topology.Circle))) from
    Diffeomorph.inner_pullbackMetricCross_comp (Φ := Φ) (g := g)
      (p := u.map (diskBoundary (x : Surgery.Topology.Circle)))
      (v := CurveMap.curvatureVector (fun θ _ => γ θ) (fun _ => g) (sigma.lift x) 0)
      (w := u.inwardConormal g (diskBoundary (x : Surgery.Topology.Circle)))]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] [IsManifold 𝓘(ℝ, E) ∞ A] in
theorem loopVelocity_postcomposeDiffeomorph [I.Boundaryless] [T2Space Q] [T2Space A]
    (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop)) (x : ℝ) :
    loopVelocity (I := 𝓘(ℝ, E)) (γ.postcomposeDiffeomorph Φ).toContinuousLoop x =
      mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (γ.toContinuousLoop (x : Surgery.Topology.Circle))
        (loopVelocity (I := I) γ.toContinuousLoop x) := by
  have hinner : MDifferentiableAt 𝓘(ℝ, ℝ) I
      (fun t : ℝ => γ.toContinuousLoop (t : Surgery.Topology.Circle)) x :=
    hγ.mdifferentiableAt (by decide)
  have hΦ : MDifferentiableAt I 𝓘(ℝ, E) (Φ : Q → A)
      (γ.toContinuousLoop (x : Surgery.Topology.Circle)) :=
    Φ.contMDiff.contMDiffAt.mdifferentiableAt (by decide)
  have h := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := 𝓘(ℝ, E))
    (f := fun t : ℝ => γ.toContinuousLoop (t : Surgery.Topology.Circle))
    (g := (Φ : Q → A)) (x := x) hΦ hinner (1 : TangentSpace 𝓘(ℝ, ℝ) x)
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (fun t : ℝ => Φ (γ.toContinuousLoop (t : Surgery.Topology.Circle))) x
        (1 : TangentSpace 𝓘(ℝ, ℝ) x) =
    mfderiv I 𝓘(ℝ, E) (Φ : Q → A) (γ.toContinuousLoop (x : Surgery.Topology.Circle))
      (loopVelocity (I := I) γ.toContinuousLoop x)
  exact h

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] [IsManifold 𝓘(ℝ, E) ∞ A] in
theorem mfderiv_eq_zero_iff_of_diffeomorph (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A)
    {p : Q} (X : TangentSpace I p) :
    mfderiv I 𝓘(ℝ, E) (Φ : Q → A) p X = 0 ↔ X = 0 := by
  constructor
  · intro h
    have hc := congrArg (mfderiv 𝓘(ℝ, E) I (fun q => Φ.symm q) (Φ p)) h
    rwa [Diffeomorph.mfderiv_symm_apply_mfderiv_apply, map_zero] at hc
  · intro h
    rw [h, map_zero]

theorem disk_curvature_inequality [hBoundary : I.Boundaryless] [hT2 : T2Space Q]
    [hCompact : CompactSpace Q]
    (g : SmoothRiemannianMetric I Q) (hdim : Module.finrank ℝ E = 3)
    (u : SmoothDisk (I := I) (Q := Q))
    (hnonconstant : ¬ ∃ q : Q, ∀ z : Disk, u.map z = q)
    (hconformal : u.IsConformal g) (hharmonic : u.IsHarmonic g)
    (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop))
    (hemb : Topology.IsEmbedding (γ : Surgery.Topology.Circle → Q))
    (himm : ∀ x, loopVelocity (I := I) γ.toContinuousLoop x ≠ 0)
    (sigma : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ theta, u.map (diskBoundary theta) = γ (sigma.map theta)) :
    IntegrableOn (diskExtension (u.sectionalDensity g)) (Metric.closedBall (0 : ℂ) 1) ∧
      IntervalIntegrable (u.boundaryCurvatureDensity g γ sigma htrace) volume 0 1 ∧
      2 * Real.pi ≤
        (∫ z in Metric.closedBall (0 : ℂ) 1, diskExtension (u.sectionalDensity g) z) +
        ∫ x in (0 : ℝ)..1, u.boundaryCurvatureDensity g γ sigma htrace x := by
  classical
  let _ := hemb
  let c : Geometry.Topology.StandardModelCopy I Q E :=
    Geometry.Topology.standardModelCopy (I := I) (M := Q) (e := ContinuousLinearEquiv.refl ℝ E)
  let _ : CompactSpace c.Q := c.equiv.toHomeomorph.compactSpace
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  have hγ' : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
      (loopLift (γ.postcomposeDiffeomorph c.equiv).toContinuousLoop) := by
    have h := c.equiv.contMDiff.comp hγ
    change ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
      (fun x : ℝ => c.equiv (γ.toContinuousLoop (x : Surgery.Topology.Circle)))
    exact h
  have himm' : ∀ x, loopVelocity (I := 𝓘(ℝ, E))
      (γ.postcomposeDiffeomorph c.equiv).toContinuousLoop x ≠ 0 := by
    intro x hzero
    rw [loopVelocity_postcomposeDiffeomorph c.equiv γ hγ x] at hzero
    exact himm x ((mfderiv_eq_zero_iff_of_diffeomorph c.equiv _).mp hzero)
  have htrace' : ∀ theta, (SmoothDisk.comp_diffeomorph c.equiv u).map (diskBoundary theta) =
      (γ.postcomposeDiffeomorph c.equiv) (sigma.map theta) := by
    intro theta
    rw [SmoothDisk.comp_diffeomorph_map, htrace theta]
    rfl
  have hnonconstant' : ¬ ∃ q : c.Q, ∀ z : Disk,
      (SmoothDisk.comp_diffeomorph c.equiv u).map z = q := by
    rintro ⟨q, hq⟩
    refine hnonconstant ⟨c.equiv.symm q, fun z => ?_⟩
    have h := hq z
    rw [SmoothDisk.comp_diffeomorph_map] at h
    rw [← h, c.equiv.symm_apply_apply]
  exact disk_curvature_inequality_of_standardModelCopy g hdim u γ sigma htrace c
    (γ.postcomposeDiffeomorph c.equiv) hγ' himm' htrace' hnonconstant'
    (SmoothDisk.isConformal_comp_diffeomorph c.equiv g u hconformal)
    (SmoothDisk.isHarmonic_comp_diffeomorph c.equiv g u hharmonic)
    (fun x => SmoothDisk.boundaryCurvatureDensity_comp_diffeomorph c.equiv g u γ hγ himm sigma
      htrace htrace' x)

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
