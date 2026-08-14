import DifferentialGeometry.Topology.Morse.Manifold
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

namespace DifferentialGeometry.Topology.Morse

open Manifold Set
open scoped Manifold ContDiff

noncomputable section

variable {n : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ (MorseModel n) H}

private theorem exists_coord_of_fderiv_ne_zero (g : MorseModel n → ℝ) (y : MorseModel n)
    (h : fderiv ℝ g y ≠ 0) :
    ∃ i : Fin n, (fderiv ℝ g y) (Pi.single i (1 : ℝ)) ≠ 0 := by
  by_contra! hz
  apply h
  apply ContinuousLinearMap.ext
  intro v
  have hv : v = ∑ i : Fin n, v i • (Pi.single i (1 : ℝ) : MorseModel n) := by
    ext i
    rw [Finset.sum_apply]
    simp [smul_eq_mul, Pi.single_apply]
  rw [hv]
  simp [hz]

private theorem chartRep_contDiffOn (I : ModelWithCorners ℝ (MorseModel n) H)
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (x₀ : M) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : MorseModel n => f ((extChartAt I x₀).symm y))
      (extChartAt I x₀).target := by
  have hc : ContMDiffOn I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f Set.univ := by
    intro x hx
    exact hf x
  have hcsub : ContMDiffOn I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f (chartAt H x₀).source :=
    hc.mono (by intro x hx; trivial)
  have hc' : ContMDiffOn 𝓘(ℝ, MorseModel n) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (f ∘ (extChartAt I x₀).symm) (extChartAt I x₀ '' (chartAt H x₀).source) :=
    (contMDiffOn_iff_source_of_mem_maximalAtlas (I := I) (I' := 𝓘(ℝ, ℝ))
    (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (e := chartAt H x₀) (IsManifold.chart_mem_maximalAtlas x₀)
    (s := (chartAt H x₀).source) (hs := by intro x hx; exact hx)).1 hcsub
  have hcd : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ (extChartAt I x₀).symm)
      (extChartAt I x₀ '' (chartAt H x₀).source) :=
    (contMDiffOn_iff_contDiffOn).1 hc'
  have hrange : extChartAt I x₀ '' (chartAt H x₀).source = (extChartAt I x₀).target := by
    exact (OpenPartialHomeomorph.extend_target_eq_image_source (f := chartAt H x₀) (I := I)).symm
  rw [show (fun y : MorseModel n => f ((extChartAt I x₀).symm y)) = f ∘ (extChartAt I x₀).symm by rfl]
  rwa [← hrange]

theorem tangentTrivializationAt_apply (I : ModelWithCorners ℝ (MorseModel n) H)
    [IsManifold I (⊤ : WithTop ℕ∞) M] (x₀ x : M)
    (hx : x ∈ (extChartAt I x₀).source) (v : TangentSpace I x) :
    (trivializationAt (MorseModel n) (TangentSpace I) x₀ ⟨x, v⟩).2 =
      (mfderiv I 𝓘(ℝ, MorseModel n) (extChartAt I x₀) x) v := by
  rw [TangentBundle.trivializationAt_apply]
  rw [mfderiv]
  have hmd : MDifferentiableAt I 𝓘(ℝ, MorseModel n) (extChartAt I x₀) x := by
    have hxsrc : x ∈ (chartAt H x₀).source := by
      rwa [extChartAt_source (I := I) (x := x₀)] at hx
    exact (contMDiffAt_extChartAt' (I := I) (n := (⊤ : WithTop ℕ∞)) (x := x₀) hxsrc).mdifferentiableAt (by norm_num)
  rw [if_pos hmd]
  change fderivWithin ℝ (extChartAt I x₀ ∘ (extChartAt I x).symm) (range I) (extChartAt I x x) v =
      fderivWithin ℝ (extChartAt I x₀ ∘ (extChartAt I x).symm) (range I) (extChartAt I x x) v
  rfl

theorem localUnitSpeedVectorField_at_noncritical (I : ModelWithCorners ℝ (MorseModel n) H)
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    {x₀ : M} (hcrit : ¬ IsCriticalPointAt I f x₀) :
    ∃ (i : Fin n),
      (fderiv ℝ (fun y : MorseModel n => f ((extChartAt I x₀).symm y)) (extChartAt I x₀ x₀))
          (Pi.single i (1 : ℝ)) ≠ 0 ∧
      ∃ W : (x : M) → TangentSpace I x,
        ∀ x ∈ (extChartAt I x₀).source,
          (fderiv ℝ (fun y : MorseModel n => f ((extChartAt I x₀).symm y)) (extChartAt I x₀ x))
              (Pi.single i (1 : ℝ)) ≠ 0 →
          (mfderiv I 𝓘(ℝ, MorseModel n) (extChartAt I x₀) x) (W x) =
              -(((fderiv ℝ (fun y : MorseModel n => f ((extChartAt I x₀).symm y)) (extChartAt I x₀ x))
                  (Pi.single i (1 : ℝ)))⁻¹) • (Pi.single i (1 : ℝ) : MorseModel n) ∧
          (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (W x)) = -1 := by
  have hgOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : MorseModel n => f ((extChartAt I x₀).symm y))
      (extChartAt I x₀).target := chartRep_contDiffOn I f hf x₀
  have hmemx₀ : extChartAt I x₀ x₀ ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source (mem_extChartAt_source x₀)
  have hcritChart : fderiv ℝ (fun y : MorseModel n => f ((extChartAt I x₀).symm y))
      (extChartAt I x₀ x₀) ≠ 0 := by
    have hiff := isCriticalPointAt_iff_chart_fderiv I f hf x₀
    intro hz
    exact hcrit (hiff.2 hz)
  rcases exists_coord_of_fderiv_ne_zero (fun y : MorseModel n => f ((extChartAt I x₀).symm y))
    (extChartAt I x₀ x₀) hcritChart with ⟨i, hi⟩
  let e : PartialEquiv M (MorseModel n) := extChartAt I x₀
  let g : MorseModel n → ℝ := fun y => f (e.symm y)
  let a : M → ℝ := fun x => (fderiv ℝ g (e x)) (Pi.single i (1 : ℝ))
  let W : (x : M) → TangentSpace I x := fun x =>
    (mfderivWithin 𝓘(ℝ, MorseModel n) I e.symm (range I) (e x)) (-(a x)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel n))
  refine ⟨i, ?_, W, ?_⟩
  · simpa [g, e] using hi
  intro x hx hane
  have hane_g : (fderiv ℝ g (e x)) (Pi.single i (1 : ℝ)) ≠ 0 := by
    simpa [g, e] using hane
  have hepx : e.symm (e x) = x := e.left_inv hx
  have hmemx : e x ∈ (extChartAt I x₀).target := e.map_source hx
  have hmdg := ((hgOn (e x) hmemx).contDiffAt ((isOpen_extChartAt_target x₀).mem_nhds hmemx)).differentiableAt
    (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  have hxsrc : x ∈ (chartAt H x₀).source := by
    rwa [extChartAt_source (I := I) (x := x₀)] at hx
  have hmdchart := (contMDiffAt_extChartAt' (I := I) (n := (⊤ : WithTop ℕ∞)) (x := x₀) hxsrc).mdifferentiableAt (by norm_num)
  have hcomp := mfderiv_comp (x := x) (g := g) (f := e) (hg := hmdg.mdifferentiableAt) (hf := hmdchart)
  have hfuneq : (fun y : M => f y) =ᶠ[nhds x] (fun y : M => g (e y)) := by
    have hsrcopen : IsOpen e.source := isOpen_extChartAt_source x₀
    exact Filter.eventuallyEq_of_mem (by simpa [e] using (hsrcopen.mem_nhds hx))
      (fun y hy => congrArg f (e.left_inv hy).symm)
  have heq := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ)) hfuneq
  have hge : mfderiv 𝓘(ℝ, MorseModel n) 𝓘(ℝ, ℝ) g (e x) = fderiv ℝ g (e x) := by
    exact (mfderiv_eq_fderiv (𝕜 := ℝ) (E := MorseModel n) (E' := ℝ) (f := g) (x := e x))
  have hid := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := x₀)
    (y := e x) (by simpa [e] using hmemx)
  have hid' : (mfderiv I 𝓘(ℝ, MorseModel n) e x) ∘L
      (mfderivWithin 𝓘(ℝ, MorseModel n) I e.symm (range I) (e x)) =
      ContinuousLinearMap.id _ _ := by
    rw [hepx] at hid
    exact hid
  have hidapply : ∀ w : MorseModel n,
      (mfderiv I 𝓘(ℝ, MorseModel n) e x)
        ((mfderivWithin 𝓘(ℝ, MorseModel n) I e.symm (range I) (e x)) w) = w := by
    intro w
    change (((mfderiv I 𝓘(ℝ, MorseModel n) e x).comp
      (mfderivWithin 𝓘(ℝ, MorseModel n) I e.symm (range I) (e x)))) w = w
    rw [hid']
    simp
  have hchartW : ((mfderiv I 𝓘(ℝ, MorseModel n) e x) : TangentSpace I x →L[ℝ] MorseModel n) (W x) =
      -(a x)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel n) := by
    dsimp [W, a]
    exact hidapply (-(a x)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel n))
  have hfinal : (fderiv ℝ g (e x)) (-(a x)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel n)) = -1 := by
    rw [(fderiv ℝ g (e x)).map_smul]
    rw [smul_eq_mul]
    have haval : (fderiv ℝ g (e x)) (Pi.single i (1 : ℝ)) = a x := by
      dsimp [a]
    rw [← haval]
    field_simp [hane_g]
  have hmain : (mfderiv I 𝓘(ℝ, ℝ) f x) (W x) = (-1 : ℝ) := by
    rw [heq]
    have hfun : (fun y : M => g (e y)) = (g ∘ e) := by rfl
    rw [hfun, hcomp]
    change ((mfderiv 𝓘(ℝ, MorseModel n) 𝓘(ℝ, ℝ) g (e x) : MorseModel n →L[ℝ] ℝ))
        (((mfderiv I 𝓘(ℝ, MorseModel n) e x) : TangentSpace I x →L[ℝ] MorseModel n) (W x)) = (-1 : ℝ)
    rw [hge]
    rw [hchartW]
    exact hfinal
  have hts : (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (W x)) =
      (mfderiv I 𝓘(ℝ, ℝ) f x) (W x) := by
    rfl
  constructor
  · change (mfderiv I 𝓘(ℝ, MorseModel n) e x) (W x) =
        -(((fderiv ℝ (fun y : MorseModel n => f (e.symm y)) (e x)) (Pi.single i (1 : ℝ)))⁻¹) •
          (Pi.single i (1 : ℝ) : MorseModel n)
    simpa [a, g] using hchartW
  · rw [hts]
    exact hmain

theorem exists_open_unitSpeedVectorField_at_noncritical (I : ModelWithCorners ℝ (MorseModel n) H)
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f)
    {x₀ : M} (hcrit : ¬ IsCriticalPointAt I f x₀) :
    ∃ (U : Set M), x₀ ∈ U ∧ IsOpen U ∧
      ∃ W : (x : M) → TangentSpace I x,
        (∀ x ∈ U, (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (W x)) = -1) ∧
        ContMDiffOn I (I.prod 𝓘(ℝ, MorseModel n)) ∞
          (fun x : M => (⟨x, W x⟩ : TangentBundle I M)) U := by
  rcases localUnitSpeedVectorField_at_noncritical I f hf hcrit with ⟨i, hi₀, W, hW⟩
  let p : M → ℝ := fun x => (fderiv ℝ (fun y : MorseModel n => f ((extChartAt I x₀).symm y))
    (extChartAt I x₀ x)) (Pi.single i (1 : ℝ))
  have hgOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : MorseModel n => f ((extChartAt I x₀).symm y))
      (extChartAt I x₀).target := chartRep_contDiffOn I f hf x₀
  have hcont : ContinuousOn p (extChartAt I x₀).source := by
    have hfd : ContDiffOn ℝ 1 (fderiv ℝ (fun y : MorseModel n => f ((extChartAt I x₀).symm y)))
        (extChartAt I x₀).target :=
      hgOn.fderiv_of_isOpen (isOpen_extChartAt_target x₀)
        (by
          change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
    have hcontfd : ContinuousOn (fderiv ℝ (fun y : MorseModel n => f ((extChartAt I x₀).symm y)))
        (extChartAt I x₀).target := hfd.continuousOn
    have hconte : ContinuousOn (extChartAt I x₀) (extChartAt I x₀).source := by
      simpa [extChartAt_source (I := I) (x := x₀)] using
        (contMDiffOn_extChartAt (I := I) (n := (⊤ : WithTop ℕ∞)) (x := x₀)).continuousOn
    have hcomp' : ContinuousOn (fun x : M =>
        (fderiv ℝ (fun y : MorseModel n => f ((extChartAt I x₀).symm y))) (extChartAt I x₀ x))
        (extChartAt I x₀).source :=
      hcontfd.comp hconte (by intro x hx; exact (extChartAt I x₀).map_source hx)
    have happly : Continuous (fun L : (MorseModel n →L[ℝ] ℝ) => L (Pi.single i (1 : ℝ))) :=
      (ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1 : ℝ)) : (MorseModel n →L[ℝ] ℝ) →L[ℝ] ℝ).cont
    simpa [p, Function.comp_def] using (happly.comp_continuousOn hcomp')
  have hmem : x₀ ∈ (extChartAt I x₀).source := mem_extChartAt_source x₀
  have hne₀ : p x₀ ≠ 0 := by
    simpa [p] using hi₀
  have hV : {x : M | p x ≠ 0} ∈ nhds x₀ := by
    have hcontAt : ContinuousAt p x₀ :=
      (hcont x₀ hmem).continuousAt ((isOpen_extChartAt_source x₀).mem_nhds hmem)
    exact hcontAt.preimage_mem_nhds (isOpen_ne.mem_nhds hne₀)
  rcases mem_nhds_iff.mp hV with ⟨V, hVsub, hVopen, hVx₀⟩
  let U : Set M := V ∩ (extChartAt I x₀).source
  have hUopen : IsOpen U := hVopen.inter (isOpen_extChartAt_source x₀)
  refine ⟨U, ?_, hUopen, W, ?_, ?_⟩
  · exact ⟨hVx₀, hmem⟩
  · intro x hx
    have hxV : x ∈ V := hx.1
    have hpx : p x ≠ 0 := hVsub hxV
    exact (hW x hx.2 (by simpa [p] using hpx)).2
  · intro x hx
    have hmd' : ContMDiffAt I (I.prod 𝓘(ℝ, MorseModel n)) ∞
        (fun x : M => (⟨x, W x⟩ : TangentBundle I M)) x := by
      rw [Bundle.Trivialization.contMDiffAt_section_iff (e := trivializationAt (MorseModel n) (TangentSpace I) x₀)]
      · have hfib : (fun y : M => (trivializationAt (MorseModel n) (TangentSpace I) x₀ ⟨y, W y⟩).2) =ᶠ[nhds x]
            (fun y : M => -((fderiv ℝ (fun z : MorseModel n => f ((extChartAt I x₀).symm z)) (extChartAt I x₀ y))
                (Pi.single i (1 : ℝ)))⁻¹ • (Pi.single i (1 : ℝ) : MorseModel n)) := by
          exact Filter.eventuallyEq_of_mem (hUopen.mem_nhds hx) (fun y hy => by
            rw [tangentTrivializationAt_apply I x₀ y hy.2 (W y)]
            exact (hW y hy.2 (by
              have hyV : y ∈ V := hy.1
              have hpy : p y ≠ 0 := hVsub hyV
              simpa [p] using hpy)).1)
        have hc : ContMDiffAt I 𝓘(ℝ, MorseModel n) ∞
            (fun y : M => -((fderiv ℝ (fun z : MorseModel n => f ((extChartAt I x₀).symm z)) (extChartAt I x₀ y))
                (Pi.single i (1 : ℝ)))⁻¹ • (Pi.single i (1 : ℝ) : MorseModel n)) x := by
          have hxU : x ∈ U := hx
          have hxVx : x ∈ V ∧ x ∈ (chartAt H x₀).source := by
            simpa [U, extChartAt_source (I := I) (x := x₀)] using hxU
          have hxsrc : x ∈ (chartAt H x₀).source := hxVx.2
          have hmemz : extChartAt I x₀ x ∈ (extChartAt I x₀).target :=
            (extChartAt I x₀).map_source hx.2
          have hpart : ContDiffAt ℝ ∞ (fun z : MorseModel n =>
              (fderiv ℝ (fun w : MorseModel n => f ((extChartAt I x₀).symm w)) z) (Pi.single i (1 : ℝ)))
              (extChartAt I x₀ x) := by
            have hfd : ContDiffOn ℝ ∞ (fderiv ℝ (fun w : MorseModel n => f ((extChartAt I x₀).symm w)))
                (extChartAt I x₀).target :=
              ((contDiffOn_infty_iff_fderiv_of_isOpen (isOpen_extChartAt_target x₀)).1
                hgOn).2
            have hc' : ContDiffOn ℝ ∞ (fun z : MorseModel n =>
                (fderiv ℝ (fun w : MorseModel n => f ((extChartAt I x₀).symm w)) z) (Pi.single i (1 : ℝ)))
                (extChartAt I x₀).target :=
              hfd.clm_apply (contDiffOn_const : ContDiffOn ℝ ∞
                (fun _ : MorseModel n => (Pi.single i (1 : ℝ) : MorseModel n)) (extChartAt I x₀).target)
            exact (hc' (extChartAt I x₀ x) hmemz).contDiffAt ((isOpen_extChartAt_target x₀).mem_nhds hmemz)
          have hne : (fderiv ℝ (fun w : MorseModel n => f ((extChartAt I x₀).symm w)) (extChartAt I x₀ x))
              (Pi.single i (1 : ℝ)) ≠ 0 := by
            simpa [p] using hVsub hx.1
          have hF : ContDiffAt ℝ ∞ (fun t : ℝ => -t⁻¹ • (Pi.single i (1 : ℝ) : MorseModel n)) (p x) := by
            have hinv : ContDiffAt ℝ ∞ (fun t : ℝ => t⁻¹) (p x) := by
              exact ContDiffAt.inv (contDiffAt_id : ContDiffAt ℝ ∞ (fun t : ℝ => t) (p x)) (by
                dsimp [p]
                exact hne)
            have hlin : (fun c : ℝ => c • (Pi.single i (1 : ℝ) : MorseModel n)) =
                ((1 : ℝ →L[ℝ] ℝ).smulRight (Pi.single i (1 : ℝ) : MorseModel n) : ℝ →L[ℝ] MorseModel n) := by
              funext c
              simp [ContinuousLinearMap.smulRight_apply]
            have hsmul : ContDiffAt ℝ ∞ (fun c : ℝ => c • (Pi.single i (1 : ℝ) : MorseModel n)) (-(p x)⁻¹) := by
              rw [hlin]
              exact ((1 : ℝ →L[ℝ] ℝ).smulRight (Pi.single i (1 : ℝ) : MorseModel n) : ℝ →L[ℝ] MorseModel n).contDiff.contDiffAt
            exact (ContDiffAt.comp (x := p x) (g := fun c : ℝ => c • (Pi.single i (1 : ℝ) : MorseModel n))
              (f := fun t : ℝ => -t⁻¹) (hg := hsmul) (hf := hinv.neg))
          have hcomp' : ContDiffAt ℝ ∞ (fun z : MorseModel n =>
              -((fderiv ℝ (fun w : MorseModel n => f ((extChartAt I x₀).symm w)) z) (Pi.single i (1 : ℝ)))⁻¹ •
                (Pi.single i (1 : ℝ) : MorseModel n)) (extChartAt I x₀ x) := by
            have hz : (fun z : MorseModel n =>
                -((fderiv ℝ (fun w : MorseModel n => f ((extChartAt I x₀).symm w)) z) (Pi.single i (1 : ℝ)))⁻¹ •
                  (Pi.single i (1 : ℝ) : MorseModel n)) =
                (fun t : ℝ => -t⁻¹ • (Pi.single i (1 : ℝ) : MorseModel n)) ∘
                  (fun z : MorseModel n => (fderiv ℝ (fun w : MorseModel n => f ((extChartAt I x₀).symm w)) z)
                    (Pi.single i (1 : ℝ))) := by
              funext z
              rfl
            rw [hz]
            exact hF.comp (extChartAt I x₀ x) hpart
          have heq : (fun z : MorseModel n =>
              -((fderiv ℝ (fun w : MorseModel n => f ((extChartAt I x₀).symm w))
                  (extChartAt I x₀ ((extChartAt I x₀).symm z))) (Pi.single i (1 : ℝ)))⁻¹ •
                (Pi.single i (1 : ℝ) : MorseModel n)) =ᶠ[nhds (extChartAt I x₀ x)]
              (fun z : MorseModel n => -((fderiv ℝ (fun w : MorseModel n => f ((extChartAt I x₀).symm w)) z)
                  (Pi.single i (1 : ℝ)))⁻¹ • (Pi.single i (1 : ℝ) : MorseModel n)) := by
            exact Filter.eventuallyEq_of_mem
              ((isOpen_extChartAt_target x₀).mem_nhds hmemz) (fun z hz => by
                have hz' : (extChartAt I x₀) ((extChartAt I x₀).symm z) = z :=
                  (extChartAt I x₀).right_inv hz
                change -((fderiv ℝ (fun w : MorseModel n => f ((extChartAt I x₀).symm w))
                    (extChartAt I x₀ ((extChartAt I x₀).symm z))) (Pi.single i (1 : ℝ)))⁻¹ •
                      (Pi.single i (1 : ℝ) : MorseModel n) =
                    -((fderiv ℝ (fun w : MorseModel n => f ((extChartAt I x₀).symm w)) z)
                      (Pi.single i (1 : ℝ)))⁻¹ • (Pi.single i (1 : ℝ) : MorseModel n)
                rw [hz'])
          have hcdComposed : ContDiffAt ℝ ∞ ((fun y : M =>
              -((fderiv ℝ (fun z : MorseModel n => f ((extChartAt I x₀).symm z)) (extChartAt I x₀ y))
                  (Pi.single i (1 : ℝ)))⁻¹ • (Pi.single i (1 : ℝ) : MorseModel n)) ∘ (extChartAt I x₀).symm)
              (extChartAt I x₀ x) := by
            exact ContDiffAt.congr_of_eventuallyEq hcomp' heq
          have hmdComposed : ContMDiffWithinAt 𝓘(ℝ, MorseModel n) 𝓘(ℝ, MorseModel n) ∞
              ((fun y : M => -((fderiv ℝ (fun z : MorseModel n => f ((extChartAt I x₀).symm z)) (extChartAt I x₀ y))
                  (Pi.single i (1 : ℝ)))⁻¹ • (Pi.single i (1 : ℝ) : MorseModel n)) ∘ (extChartAt I x₀).symm)
              (range I) (extChartAt I x₀ x) := by
            exact (contMDiffWithinAt_iff_contDiffWithinAt.mpr hcdComposed.contDiffWithinAt)
          rw [contMDiffAt_iff_source_of_mem_source (x := x₀) (x' := x) hxsrc]
          exact hmdComposed
        exact ContMDiffAt.congr_of_eventuallyEq hc hfib
      · simpa [U] using hx.2
    exact hmd'.contMDiffWithinAt (s := U)

theorem exists_unitSpeedVectorField_on_compact (I : ModelWithCorners ℝ (MorseModel n) H)
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (K : Set M)
    (hcompact : IsCompact K)
    (hregular : ∀ x ∈ K, ¬ IsCriticalPointAt I f x) :
    ∃ V : (x : M) → TangentSpace I x,
      ContMDiff I (I.prod 𝓘(ℝ, MorseModel n)) ∞
        (fun x : M => (⟨x, V x⟩ : TangentBundle I M)) ∧
      IsCompact (tsupport V) ∧
      (∀ x ∈ K,
        (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (V x)) = -1) ∧
      (∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (V x)) ∧
        (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (V x)) ≤ 0) := by
  let K : Set M := K
  have hpts : ∀ x : K, ∃ U : Set M, x.1 ∈ U ∧ IsOpen U ∧ ∃ W : (x : M) → TangentSpace I x,
      (∀ y ∈ U, (NormedSpace.fromTangentSpace (f y)) ((mfderiv I 𝓘(ℝ, ℝ) f y) (W y)) = -1) ∧
      ContMDiffOn I (I.prod 𝓘(ℝ, MorseModel n)) ∞
        (fun y : M => (⟨y, W y⟩ : TangentBundle I M)) U :=
    fun x => exists_open_unitSpeedVectorField_at_noncritical I f hf (hregular x x.2)
  choose U hUmem hUopen W hWdf hWsec using hpts
  have hKclosed : IsClosed K := hcompact.isClosed
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  rcases exists_open_between_and_isCompact_closure hcompact isOpen_univ (subset_univ K)
    with ⟨W₀, hW₀open, hKW₀, hW₀cl, hW₀compact⟩
  let U' : K → Set M := fun x => U x ∩ W₀
  have hU'mem : ∀ x : K, x.1 ∈ U' x := fun x => ⟨hUmem x, hKW₀ x.2⟩
  have hU'open : ∀ x : K, IsOpen (U' x) := fun x => (hUopen x).inter hW₀open
  have hcov : K ⊆ ⋃ x : K, U' x := by
    intro y hy
    exact Set.mem_iUnion_of_mem ⟨y, hy⟩ (hU'mem ⟨y, hy⟩)
  rcases SmoothPartitionOfUnity.exists_isSubordinate (I := I) (s := K) (U := U')
    (hs := hKclosed) (ho := hU'open) (hU := hcov) with ⟨ρ, hρsub⟩
  let V : (x : M) → TangentSpace I x := fun y => ∑ᶠ x : K, (ρ x y : ℝ) • (W x y : TangentSpace I y)
  have hdfsum : ∀ y : M,
      (NormedSpace.fromTangentSpace (f y)) ((mfderiv I 𝓘(ℝ, ℝ) f y) (V y)) =
        -(∑ᶠ x : K, (ρ x y : ℝ)) := by
    intro y
    let L : TangentSpace I y →L[ℝ] ℝ :=
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f y) : TangentSpace 𝓘(ℝ, ℝ) (f y) →L[ℝ] ℝ).comp
        (mfderiv I 𝓘(ℝ, ℝ) f y)
    have hVdef : (NormedSpace.fromTangentSpace (f y)) ((mfderiv I 𝓘(ℝ, ℝ) f y) (V y)) = L (V y) := by
      simp [L]
    rw [hVdef]
    have hfinSuppρ : Function.HasFiniteSupport (fun x : K => ρ x y) := by
      have hlf : LocallyFinite (fun x : K => {z : M | ρ x z ≠ 0}) := ρ.locallyFinite
      have hlfy := hlf y
      rcases hlfy with ⟨N, hN, hfinN⟩
      have hsub : (Function.support fun x : K => ρ x y) ⊆
          {x : K | ((fun x : K => {z : M | ρ x z ≠ 0}) x ∩ N).Nonempty} := by
        intro x hx
        rw [Function.support] at hx
        exact ⟨y, ⟨hx, mem_of_mem_nhds hN⟩⟩
      exact Set.Finite.subset hfinN hsub
    have hfinSupp : Function.HasFiniteSupport (fun x : K => ρ x y • W x y) := by
      exact Set.Finite.subset hfinSuppρ (by intro x hx; exact fun hρ0 => hx (by simp [hρ0]))
    have hlin : L (V y) = ∑ᶠ x : K, L (ρ x y • W x y) := by
      dsimp [V]
      have hmap := (AddMonoidHom.map_finsum (g := (L : TangentSpace I y →+ ℝ)) (hf := hfinSupp))
      simpa using hmap
    rw [hlin]
    have hterm : ∀ x : K, L (ρ x y • W x y) = ρ x y • L (W x y) := by
      intro x
      rw [map_smul]
    have hrew : (∑ᶠ x : K, L (ρ x y • W x y)) = ∑ᶠ x : K, ρ x y • (-1 : ℝ) := by
      apply finsum_congr
      intro x
      rw [hterm x]
      by_cases hyU : y ∈ U' x
      · have hdf := hWdf x y hyU.1
        have hLval : L (W x y) = -1 := by
          dsimp [L]
          simpa using hdf
        rw [hLval]
      · have hρ0 : ρ x y = 0 := by
          have hts' : y ∉ tsupport (ρ x) := fun h => hyU (hρsub x h)
          have hnot : y ∉ Function.support (ρ x) := fun hs => hts' (subset_closure hs)
          by_contra h
          exact hnot (by simpa [Function.support] using h)
        simp [hρ0]
    rw [hrew]
    have hsum : (∑ᶠ x : K, ρ x y • (-1 : ℝ)) = -(∑ᶠ x : K, (ρ x y : ℝ)) := by
      have hsmul' : (∑ᶠ x : K, ρ x y • (-1 : ℝ)) = (∑ᶠ x : K, ρ x y) • (-1 : ℝ) := by
        exact (finsum_smul' hfinSuppρ (-1 : ℝ)).symm
      rw [hsmul']
      simp
    exact hsum
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · have hsummand : ∀ x : K, ContMDiff I (I.prod 𝓘(ℝ, MorseModel n)) ∞
        (fun y : M => (⟨y, ρ x y • W x y⟩ : TangentBundle I M)) := by
      intro x
      have hcoerce : (ρ x : M → ℝ) = (ρ x).1 := rfl
      have hρOn : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (ρ x : M → ℝ) (U' x) := by
        have hc' : ContMDiffOn I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ρ x : M → ℝ) Set.univ := by
          simpa [hcoerce] using (ρ x).property.contMDiffOn
        exact (hc'.mono (subset_univ _)).of_le le_rfl
      exact (ContMDiffOn.smul_section_of_tsupport (u := U' x) hρOn (hU'open x) (hρsub x)
        ((hWsec x).mono (by intro y hy; exact hy.1)))
    have hfin : LocallyFinite (fun x : K => {y : M | ρ x y • W x y ≠ 0}) := by
      exact ρ.locallyFinite.subset (fun x => by
        intro y hy
        have hρy : ρ x y ≠ 0 := by
          intro hρ0
          apply hy
          simp [hρ0]
        exact hρy)
    simpa [V] using (ContMDiff.finsum_section_of_locallyFinite hfin hsummand)
  · have hmem : ∀ y, y ∈ Function.support V → y ∈ ⋃ x : K, tsupport (ρ x) := by
      intro y hy
      by_contra hnot
      have hy' : V y ≠ 0 := hy
      apply hy'
      have hall : ∀ x : K, (ρ x y : ℝ) • (W x y : TangentSpace I y) = 0 := by
        intro x
        by_contra hx
        apply hnot
        exact Set.mem_iUnion.mpr ⟨x, subset_closure (by
          intro hρ0
          apply hx
          simp [hρ0])⟩
      have hV0 : (∑ᶠ x : K, (ρ x y : ℝ) • (W x y : TangentSpace I y)) = 0 :=
        finsum_eq_zero_of_forall_eq_zero hall
      simpa [V] using hV0
    have hsupp₀ : Function.support V ⊆ W₀ := by
      intro y hy
      rcases Set.mem_iUnion.mp (hmem y hy) with ⟨x, hx⟩
      exact (hρsub x hx).2
    have hts : tsupport V ⊆ closure W₀ := closure_mono hsupp₀
    exact hW₀compact.of_isClosed_subset (isClosed_tsupport V) hts
  · intro y hy
    rw [hdfsum y]
    have hs1 : (∑ᶠ x : K, ρ x y) = 1 := ρ.sum_eq_one hy
    rw [hs1]
  · intro y
    rw [hdfsum y]
    have hnonneg : 0 ≤ ∑ᶠ x : K, (ρ x y : ℝ) := finsum_nonneg (fun x => ρ.nonneg x y)
    have hle1 : (∑ᶠ x : K, (ρ x y : ℝ)) ≤ 1 := ρ.sum_le_one y
    constructor <;> linarith

theorem exists_unitSpeedVectorField_on_strip (I : ModelWithCorners ℝ (MorseModel n) H)
    [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f) (a b : ℝ)
    (hcompact : IsCompact (f ⁻¹' Set.Icc a b))
    (hregular : ∀ x ∈ f ⁻¹' Set.Icc a b, ¬ IsCriticalPointAt I f x) :
    ∃ V : (x : M) → TangentSpace I x,
      ContMDiff I (I.prod 𝓘(ℝ, MorseModel n)) ∞
        (fun x : M => (⟨x, V x⟩ : TangentBundle I M)) ∧
      IsCompact (tsupport V) ∧
      (∀ x ∈ f ⁻¹' Set.Icc a b,
        (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (V x)) = -1) ∧
      (∀ x, -1 ≤ (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (V x)) ∧
        (NormedSpace.fromTangentSpace (f x)) ((mfderiv I 𝓘(ℝ, ℝ) f x) (V x)) ≤ 0) := by
  let K : Set M := f ⁻¹' Set.Icc a b
  have hpts : ∀ x : K, ∃ U : Set M, x.1 ∈ U ∧ IsOpen U ∧ ∃ W : (x : M) → TangentSpace I x,
      (∀ y ∈ U, (NormedSpace.fromTangentSpace (f y)) ((mfderiv I 𝓘(ℝ, ℝ) f y) (W y)) = -1) ∧
      ContMDiffOn I (I.prod 𝓘(ℝ, MorseModel n)) ∞
        (fun y : M => (⟨y, W y⟩ : TangentBundle I M)) U :=
    fun x => exists_open_unitSpeedVectorField_at_noncritical I f hf (hregular x x.2)
  choose U hUmem hUopen W hWdf hWsec using hpts
  have hKclosed : IsClosed K := hcompact.isClosed
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  rcases exists_open_between_and_isCompact_closure hcompact isOpen_univ (subset_univ K)
    with ⟨W₀, hW₀open, hKW₀, hW₀cl, hW₀compact⟩
  let U' : K → Set M := fun x => U x ∩ W₀
  have hU'mem : ∀ x : K, x.1 ∈ U' x := fun x => ⟨hUmem x, hKW₀ x.2⟩
  have hU'open : ∀ x : K, IsOpen (U' x) := fun x => (hUopen x).inter hW₀open
  have hcov : K ⊆ ⋃ x : K, U' x := by
    intro y hy
    exact Set.mem_iUnion_of_mem ⟨y, hy⟩ (hU'mem ⟨y, hy⟩)
  rcases SmoothPartitionOfUnity.exists_isSubordinate (I := I) (s := K) (U := U')
    (hs := hKclosed) (ho := hU'open) (hU := hcov) with ⟨ρ, hρsub⟩
  let V : (x : M) → TangentSpace I x := fun y => ∑ᶠ x : K, (ρ x y : ℝ) • (W x y : TangentSpace I y)
  have hdfsum : ∀ y : M,
      (NormedSpace.fromTangentSpace (f y)) ((mfderiv I 𝓘(ℝ, ℝ) f y) (V y)) =
        -(∑ᶠ x : K, (ρ x y : ℝ)) := by
    intro y
    let L : TangentSpace I y →L[ℝ] ℝ :=
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f y) : TangentSpace 𝓘(ℝ, ℝ) (f y) →L[ℝ] ℝ).comp
        (mfderiv I 𝓘(ℝ, ℝ) f y)
    have hVdef : (NormedSpace.fromTangentSpace (f y)) ((mfderiv I 𝓘(ℝ, ℝ) f y) (V y)) = L (V y) := by
      simp [L]
    rw [hVdef]
    have hfinSuppρ : Function.HasFiniteSupport (fun x : K => ρ x y) := by
      have hlf : LocallyFinite (fun x : K => {z : M | ρ x z ≠ 0}) := ρ.locallyFinite
      have hlfy := hlf y
      rcases hlfy with ⟨N, hN, hfinN⟩
      have hsub : (Function.support fun x : K => ρ x y) ⊆
          {x : K | ((fun x : K => {z : M | ρ x z ≠ 0}) x ∩ N).Nonempty} := by
        intro x hx
        rw [Function.support] at hx
        exact ⟨y, ⟨hx, mem_of_mem_nhds hN⟩⟩
      exact Set.Finite.subset hfinN hsub
    have hfinSupp : Function.HasFiniteSupport (fun x : K => ρ x y • W x y) := by
      exact Set.Finite.subset hfinSuppρ (by intro x hx; exact fun hρ0 => hx (by simp [hρ0]))
    have hlin : L (V y) = ∑ᶠ x : K, L (ρ x y • W x y) := by
      dsimp [V]
      have hmap := (AddMonoidHom.map_finsum (g := (L : TangentSpace I y →+ ℝ)) (hf := hfinSupp))
      simpa using hmap
    rw [hlin]
    have hterm : ∀ x : K, L (ρ x y • W x y) = ρ x y • L (W x y) := by
      intro x
      rw [map_smul]
    have hrew : (∑ᶠ x : K, L (ρ x y • W x y)) = ∑ᶠ x : K, ρ x y • (-1 : ℝ) := by
      apply finsum_congr
      intro x
      rw [hterm x]
      by_cases hyU : y ∈ U' x
      · have hdf := hWdf x y hyU.1
        have hLval : L (W x y) = -1 := by
          dsimp [L]
          simpa using hdf
        rw [hLval]
      · have hρ0 : ρ x y = 0 := by
          have hts' : y ∉ tsupport (ρ x) := fun h => hyU (hρsub x h)
          have hnot : y ∉ Function.support (ρ x) := fun hs => hts' (subset_closure hs)
          by_contra h
          exact hnot (by simpa [Function.support] using h)
        simp [hρ0]
    rw [hrew]
    have hsum : (∑ᶠ x : K, ρ x y • (-1 : ℝ)) = -(∑ᶠ x : K, (ρ x y : ℝ)) := by
      have hsmul' : (∑ᶠ x : K, ρ x y • (-1 : ℝ)) = (∑ᶠ x : K, ρ x y) • (-1 : ℝ) := by
        exact (finsum_smul' hfinSuppρ (-1 : ℝ)).symm
      rw [hsmul']
      simp
    exact hsum
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · have hsummand : ∀ x : K, ContMDiff I (I.prod 𝓘(ℝ, MorseModel n)) ∞
        (fun y : M => (⟨y, ρ x y • W x y⟩ : TangentBundle I M)) := by
      intro x
      have hcoerce : (ρ x : M → ℝ) = (ρ x).1 := rfl
      have hρOn : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (ρ x : M → ℝ) (U' x) := by
        have hc' : ContMDiffOn I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) (ρ x : M → ℝ) Set.univ := by
          simpa [hcoerce] using (ρ x).property.contMDiffOn
        exact (hc'.mono (subset_univ _)).of_le le_rfl
      exact (ContMDiffOn.smul_section_of_tsupport (u := U' x) hρOn (hU'open x) (hρsub x)
        ((hWsec x).mono (by intro y hy; exact hy.1)))
    have hfin : LocallyFinite (fun x : K => {y : M | ρ x y • W x y ≠ 0}) := by
      exact ρ.locallyFinite.subset (fun x => by
        intro y hy
        have hρy : ρ x y ≠ 0 := by
          intro hρ0
          apply hy
          simp [hρ0]
        exact hρy)
    simpa [V] using (ContMDiff.finsum_section_of_locallyFinite hfin hsummand)
  · have hmem : ∀ y, y ∈ Function.support V → y ∈ ⋃ x : K, tsupport (ρ x) := by
      intro y hy
      by_contra hnot
      have hy' : V y ≠ 0 := hy
      apply hy'
      have hall : ∀ x : K, (ρ x y : ℝ) • (W x y : TangentSpace I y) = 0 := by
        intro x
        by_contra hx
        apply hnot
        exact Set.mem_iUnion.mpr ⟨x, subset_closure (by
          intro hρ0
          apply hx
          simp [hρ0])⟩
      have hV0 : (∑ᶠ x : K, (ρ x y : ℝ) • (W x y : TangentSpace I y)) = 0 :=
        finsum_eq_zero_of_forall_eq_zero hall
      simpa [V] using hV0
    have hsupp₀ : Function.support V ⊆ W₀ := by
      intro y hy
      rcases Set.mem_iUnion.mp (hmem y hy) with ⟨x, hx⟩
      exact (hρsub x hx).2
    have hts : tsupport V ⊆ closure W₀ := closure_mono hsupp₀
    exact hW₀compact.of_isClosed_subset (isClosed_tsupport V) hts
  · intro y hy
    rw [hdfsum y]
    have hs1 : (∑ᶠ x : K, ρ x y) = 1 := ρ.sum_eq_one hy
    rw [hs1]
  · intro y
    rw [hdfsum y]
    have hnonneg : 0 ≤ ∑ᶠ x : K, (ρ x y : ℝ) := finsum_nonneg (fun x => ρ.nonneg x y)
    have hle1 : (∑ᶠ x : K, (ρ x y : ℝ)) ≤ 1 := ρ.sum_le_one y
    constructor <;> linarith

end

end DifferentialGeometry.Topology.Morse
