import DifferentialGeometry.Topology.Morse.RegularVectorField
import DifferentialGeometry.Topology.Morse.RegularSublevel
import DifferentialGeometry.Analysis.ODE.CompactSupportFlow

namespace DifferentialGeometry.Topology.Morse

open Manifold Set Filter DifferentialGeometry.Analysis.ODE
open scoped Manifold ContDiff Topology Filter

noncomputable section

variable {m : ℕ} {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]

private theorem familyChartRep_contDiffOn
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (F : M → ℝ → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2)) (x₀ : M) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : MorseModel (m + 1) × ℝ => F ((extChartAt I x₀).symm q.1) q.2)
      ((extChartAt I x₀).target ×ˢ Set.univ) := by
  have hFOn : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2) Set.univ := by
    intro x hx
    exact hF x
  have hc' : ContMDiffOn 𝓘(ℝ, MorseModel (m + 1) × ℝ) 𝓘(ℝ, ℝ)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : MorseModel (m + 1) × ℝ =>
        F ((extChartAt I x₀).symm q.1) q.2)
      ((extChartAt I x₀).target ×ˢ Set.univ) := by
    have hraw := (contMDiffOn_iff_source_of_mem_maximalAtlas
      (I := I.prod 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
      (f := fun q : M × ℝ => F q.1 q.2) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
      (e := chartAt (ModelProd H ℝ) (x₀, (0 : ℝ)))
      (IsManifold.chart_mem_maximalAtlas (M := M × ℝ) (x₀, (0 : ℝ)))
      (s := (chartAt H x₀).source ×ˢ Set.univ)
      (hs := by intro x hx; exact ⟨hx.1, trivial⟩)).1
      (hFOn.mono (by intro x hx; trivial))
    convert hraw using 1
    ext q
    constructor
    · rintro ⟨⟨hq1, hq2⟩, hq3⟩
      refine ⟨((chartAt H x₀).symm (I.symm q.1), q.2), ⟨?_, hq3⟩, ?_⟩
      · exact (chartAt H x₀).symm.mapsTo hq2
      · change (I (chartAt H x₀ ((chartAt H x₀).symm (I.symm q.1))), q.2) = q
        apply Prod.ext
        · ext i
          rw [show chartAt H x₀ ((chartAt H x₀).symm (I.symm q.1)) = I.symm q.1 by
            exact (chartAt H x₀).right_inv hq2]
          exact congrFun (I.right_inv (by simpa [ModelWithCorners.target_eq] using hq1)) i
        · rfl
    · rintro ⟨a, ha, hx⟩
      have hx1 : I (chartAt H x₀ a.1) = q.1 := congrArg Prod.fst hx
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [← hx1]
        simp [ModelWithCorners.target_eq]
      · rw [← hx1]
        change I.symm (I (chartAt H x₀ a.1)) ∈ (chartAt H x₀).target
        simpa using (chartAt H x₀).mapsTo ha.1
      · trivial
  exact (contMDiffOn_iff_contDiffOn (𝕜 := ℝ) (E := MorseModel (m + 1) × ℝ) (E' := ℝ)
    (f := fun q : MorseModel (m + 1) × ℝ => F ((extChartAt I x₀).symm q.1) q.2)
    (s := (extChartAt I x₀).target ×ˢ Set.univ) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))).1 hc'

private theorem familyChartRep_fderiv_apply_contDiffOn
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (F : M → ℝ → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2)) (x₀ : M) (i : Fin (m + 1)) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (MorseModel (m + 1)) × ℝ =>
        (fderiv ℝ (fun q' : (MorseModel (m + 1)) × ℝ => F ((extChartAt I x₀).symm q'.1) q'.2) q)
          (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ (Pi.single i (1 : ℝ))))
      ((extChartAt I x₀).target ×ˢ Set.univ) := by
  have hgOn := familyChartRep_contDiffOn (I := I) F hF x₀
  have hfderiv : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fderiv ℝ (fun q : (MorseModel (m + 1)) × ℝ => F ((extChartAt I x₀).symm q.1) q.2))
      ((extChartAt I x₀).target ×ˢ Set.univ) := by
    exact ((contDiffOn_infty_iff_fderiv_of_isOpen
      (IsOpen.prod (isOpen_extChartAt_target x₀) isOpen_univ)).1 hgOn).2
  exact hfderiv.clm_apply (contDiffOn_const : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
    (fun _ : (MorseModel (m + 1)) × ℝ =>
      ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ (Pi.single i (1 : ℝ)))
    ((extChartAt I x₀).target ×ˢ Set.univ))

private theorem familyChartRep_fderiv_curry
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (F : M → ℝ → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2)) (x₀ : M) (y : MorseModel (m + 1)) (s : ℝ)
    (hy : y ∈ (extChartAt I x₀).target) :
    fderiv ℝ (fun z : MorseModel (m + 1) => F ((extChartAt I x₀).symm z) s) y =
      (fderiv ℝ (fun q : (MorseModel (m + 1)) × ℝ => F ((extChartAt I x₀).symm q.1) q.2) (y, s)).comp
        (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ) := by
  let g : (MorseModel (m + 1)) × ℝ → ℝ := fun q => F ((extChartAt I x₀).symm q.1) q.2
  have hgOn := familyChartRep_contDiffOn (I := I) F hF x₀
  have hmem : (y, s) ∈ (extChartAt I x₀).target ×ˢ Set.univ := ⟨hy, trivial⟩
  have hgdiff : DifferentiableAt ℝ g (y, s) := by
    exact ((hgOn (y, s) hmem).contDiffAt
      ((IsOpen.prod (isOpen_extChartAt_target x₀) isOpen_univ).mem_nhds hmem)).differentiableAt
      (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  have hpair : HasFDerivAt (fun z : MorseModel (m + 1) => (z, s))
      (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ) y := by
    exact hasFDerivAt_prodMk_left y s
  have hfd : HasFDerivAt (fun z : MorseModel (m + 1) => g (z, s))
      ((fderiv ℝ g (y, s)).comp (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ)) y := by
    simpa [g] using (hgdiff.hasFDerivAt.comp y hpair)
  simpa [g] using hfd.fderiv

private theorem familyChartRep_fderiv_curry_time
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (F : M → ℝ → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2)) (x₀ : M) (y : MorseModel (m + 1)) (s : ℝ)
    (hy : y ∈ (extChartAt I x₀).target) :
    fderiv ℝ (fun t : ℝ => F ((extChartAt I x₀).symm y) t) s =
      (fderiv ℝ (fun q : (MorseModel (m + 1)) × ℝ => F ((extChartAt I x₀).symm q.1) q.2) (y, s)).comp
        (ContinuousLinearMap.inr ℝ (MorseModel (m + 1)) ℝ) := by
  let g : (MorseModel (m + 1)) × ℝ → ℝ := fun q => F ((extChartAt I x₀).symm q.1) q.2
  have hgOn := familyChartRep_contDiffOn (I := I) F hF x₀
  have hmem : (y, s) ∈ (extChartAt I x₀).target ×ˢ Set.univ := ⟨hy, trivial⟩
  have hgdiff : DifferentiableAt ℝ g (y, s) := by
    exact ((hgOn (y, s) hmem).contDiffAt
      ((IsOpen.prod (isOpen_extChartAt_target x₀) isOpen_univ).mem_nhds hmem)).differentiableAt
      (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  have hpair : HasFDerivAt (fun t : ℝ => (y, t))
      (ContinuousLinearMap.inr ℝ (MorseModel (m + 1)) ℝ) s := by
    exact hasFDerivAt_prodMk_right y s
  have hfd : HasFDerivAt (fun t : ℝ => g (y, t))
      ((fderiv ℝ g (y, s)).comp (ContinuousLinearMap.inr ℝ (MorseModel (m + 1)) ℝ)) s := by
    simpa [g] using (hgdiff.hasFDerivAt.comp s hpair)
  simpa [g] using hfd.fderiv

private theorem familyTimeDeriv_contMDiffOn
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (F : M → ℝ → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2)) (x₀ : M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : M × ℝ => (fderiv ℝ (fun t : ℝ => F p.1 t) p.2) 1)
      ((extChartAt I x₀).source ×ˢ Set.univ) := by
  let g : (MorseModel (m + 1)) × ℝ → ℝ := fun q => F ((extChartAt I x₀).symm q.1) q.2
  have hgOn := familyChartRep_contDiffOn (I := I) F hF x₀
  have hfderiv : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fderiv ℝ g) ((extChartAt I x₀).target ×ˢ Set.univ) := by
    exact ((contDiffOn_infty_iff_fderiv_of_isOpen
      (IsOpen.prod (isOpen_extChartAt_target x₀) isOpen_univ)).1 hgOn).2
  have ha' : ContMDiffOn 𝓘(ℝ, (MorseModel (m + 1)) × ℝ) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (MorseModel (m + 1)) × ℝ =>
        (fderiv ℝ g q) (ContinuousLinearMap.inr ℝ (MorseModel (m + 1)) ℝ (1 : ℝ)))
      ((extChartAt I x₀).target ×ˢ Set.univ) := by
    exact (contMDiffOn_iff_contDiffOn (𝕜 := ℝ) (E := (MorseModel (m + 1)) × ℝ) (E' := ℝ)
      (f := fun q : (MorseModel (m + 1)) × ℝ =>
        (fderiv ℝ g q) (ContinuousLinearMap.inr ℝ (MorseModel (m + 1)) ℝ (1 : ℝ)))
      (s := (extChartAt I x₀).target ×ˢ Set.univ) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))).2
      (hfderiv.clm_apply (contDiffOn_const : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun _ : (MorseModel (m + 1)) × ℝ =>
          ContinuousLinearMap.inr ℝ (MorseModel (m + 1)) ℝ (1 : ℝ))
        ((extChartAt I x₀).target ×ˢ Set.univ)))
  have hφ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, (MorseModel (m + 1)) × ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : M × ℝ => ((extChartAt I x₀) p.1, p.2))
      ((extChartAt I x₀).source ×ˢ Set.univ) := by
    have hc := contMDiffOn_extChartAt (I := I.prod 𝓘(ℝ, ℝ)) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
      (x := (x₀, (0 : ℝ)))
    simpa [extChartAt_prod, extChartAt_source (I := I) (x := x₀)] using hc
  exact (ha'.comp hφ (by intro p hp; exact ⟨(extChartAt I x₀).map_source hp.1, trivial⟩)).congr
    (by
      intro p hp
      have hcurry := familyChartRep_fderiv_curry_time (I := I) F hF x₀ (extChartAt I x₀ p.1) p.2
        ((extChartAt I x₀).map_source hp.1)
      have happly : (fderiv ℝ g ((extChartAt I x₀) p.1, p.2))
          (ContinuousLinearMap.inr ℝ (MorseModel (m + 1)) ℝ (1 : ℝ)) =
          ((fderiv ℝ g ((extChartAt I x₀) p.1, p.2)).comp
            (ContinuousLinearMap.inr ℝ (MorseModel (m + 1)) ℝ)) (1 : ℝ) := by
        rfl
      change (fderiv ℝ (fun t : ℝ => F p.1 t) p.2) 1 =
        (fderiv ℝ g ((extChartAt I x₀) p.1, p.2))
          (ContinuousLinearMap.inr ℝ (MorseModel (m + 1)) ℝ (1 : ℝ))
      rw [happly, ← hcurry]
      have hsymm : (extChartAt I x₀).symm ((extChartAt I x₀) p.1) = p.1 :=
        (extChartAt I x₀).left_inv hp.1
      rw [hsymm])

private theorem familyTimeDeriv_contMDiff
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (F : M → ℝ → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2)) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : M × ℝ => (fderiv ℝ (fun t : ℝ => F p.1 t) p.2) 1) := by
  intro p
  have hOn := familyTimeDeriv_contMDiffOn (I := I) F hF p.1
  have hsrc : p ∈ (extChartAt I p.1).source ×ˢ Set.univ := ⟨mem_extChartAt_source p.1, trivial⟩
  exact (hOn p hsrc).mono_of_mem_nhdsWithin (by
    have hC : (extChartAt I p.1).source ×ˢ Set.univ ∈ nhds p :=
      (IsOpen.prod (isOpen_extChartAt_source p.1) isOpen_univ).mem_nhds
        ⟨mem_extChartAt_source p.1, trivial⟩
    exact (mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨(extChartAt I p.1).source ×ˢ Set.univ, hC, inter_subset_left⟩))

private theorem family_mfderiv_decomp
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (F : M → ℝ → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2)) (x : M) (s : ℝ)
    (w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s)) :
    (NormedSpace.fromTangentSpace (F x s)) ((mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
        (fun q : M × ℝ => F q.1 q.2) (x, s)) w) =
      (NormedSpace.fromTangentSpace (F x s)) ((mfderiv I 𝓘(ℝ, ℝ) (fun y : M => F y s) x)
        ((mfderiv (I.prod 𝓘(ℝ, ℝ)) I (fun q : M × ℝ => q.1) (x, s)) w)) +
        ((fderiv ℝ (fun t : ℝ => F x t) s) 1) *
          (NormedSpace.fromTangentSpace (s : ℝ))
            ((mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : M × ℝ => q.2) (x, s)) w) := by
  let Fp : M × ℝ → ℝ := fun q => F q.1 q.2
  let w₁ : TangentSpace I x := (mfderiv (I.prod 𝓘(ℝ, ℝ)) I (fun q : M × ℝ => q.1) (x, s)) w
  let w₂ : TangentSpace 𝓘(ℝ, ℝ) s := (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : M × ℝ => q.2) (x, s)) w
  let inlMap : M → M × ℝ := fun y => (y, s)
  let inrMap : ℝ → M × ℝ := fun t => (x, t)
  have hFp : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Fp (x, s) :=
    (hF (x, s)).mdifferentiableAt (by norm_num)
  have hπ₁ : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I (fun q : M × ℝ => q.1) (x, s) :=
    mdifferentiableAt_fst
  have hπ₂ : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : M × ℝ => q.2) (x, s) :=
    mdifferentiableAt_snd
  have hinl : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ)) inlMap x := by
    exact (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  have hinr : MDifferentiableAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) inrMap s := by
    exact (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have hw₁ : w₁ = (show TangentSpace I x from w.1) := by
    dsimp [w₁]
    have hm := mfderiv_fst (𝕜 := ℝ) (E := MorseModel (m + 1)) (H := H) (I := I) (M := M)
      (E' := ℝ) (H' := ℝ) (I' := 𝓘(ℝ, ℝ)) (M' := ℝ) (x := (x, s))
    have hv : w = (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (w.1, w.2)) := by
      rfl
    rw [hv]
    rw [show (mfderiv (I.prod 𝓘(ℝ, ℝ)) I Prod.fst (x, s)) =
        ContinuousLinearMap.fst ℝ (TangentSpace I x) (TangentSpace 𝓘(ℝ, ℝ) s) from hm]
    change (ContinuousLinearMap.fst ℝ (TangentSpace I x) (TangentSpace 𝓘(ℝ, ℝ) s))
        (show TangentSpace I x × TangentSpace 𝓘(ℝ, ℝ) s from
          (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (w.1, w.2))) =
      (show TangentSpace I x from w.1)
    change (show TangentSpace I x from w.1) = (show TangentSpace I x from w.1)
    rfl
  have hw₂ : w₂ = (show TangentSpace 𝓘(ℝ, ℝ) s from w.2) := by
    dsimp [w₂]
    have hm := mfderiv_snd (𝕜 := ℝ) (E := MorseModel (m + 1)) (H := H) (I := I) (M := M)
      (E' := ℝ) (H' := ℝ) (I' := 𝓘(ℝ, ℝ)) (M' := ℝ) (x := (x, s))
    have hv : w = (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (w.1, w.2)) := by
      rfl
    rw [hv]
    rw [show (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.snd (x, s)) =
        ContinuousLinearMap.snd ℝ (TangentSpace I x) (TangentSpace 𝓘(ℝ, ℝ) s) from hm]
    change (ContinuousLinearMap.snd ℝ (TangentSpace I x) (TangentSpace 𝓘(ℝ, ℝ) s))
        (show TangentSpace I x × TangentSpace 𝓘(ℝ, ℝ) s from
          (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (w.1, w.2))) =
      (show TangentSpace 𝓘(ℝ, ℝ) s from w.2)
    change (show TangentSpace 𝓘(ℝ, ℝ) s from w.2) = (show TangentSpace 𝓘(ℝ, ℝ) s from w.2)
    rfl
  have hinlval : (mfderiv I (I.prod 𝓘(ℝ, ℝ)) inlMap x) w₁ =
      (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from
        (w₁, (0 : TangentSpace 𝓘(ℝ, ℝ) s))) := by
    have hid : MDifferentiableAt I I (fun y : M => y) x := mdifferentiableAt_id
    have hc : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun _ : M => s) x := mdifferentiableAt_const
    have hprod := mfderiv_prodMk (hf := hid) (hg := hc)
    change (mfderiv I (I.prod 𝓘(ℝ, ℝ)) (fun y : M => (y, s)) x) w₁ =
      (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (w₁, (0 : TangentSpace 𝓘(ℝ, ℝ) s)))
    rw [hprod]
    change (((mfderiv I I (fun y : M => y) x) w₁),
        ((mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => s) x) w₁)) =
      (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (w₁, (0 : TangentSpace 𝓘(ℝ, ℝ) s)))
    have hidv : (mfderiv I I (fun y : M => y) x) w₁ = w₁ := by
      change ((mfderiv I I (@id M) x) w₁) = w₁
      rw [show (mfderiv I I (@id M) x) = ContinuousLinearMap.id ℝ (TangentSpace I x) by
        exact mfderiv_id (𝕜 := ℝ) (E := MorseModel (m + 1)) (H := H) (I := I) (M := M) (x := x)]
      rfl
    have hcv : (mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => s) x) w₁ = (0 : TangentSpace 𝓘(ℝ, ℝ) s) := by
      have hm := mfderiv_const (𝕜 := ℝ) (I := I) (I' := 𝓘(ℝ, ℝ)) (x := x) (c := s)
      rw [show (mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => s) x) =
          (0 : TangentSpace I x →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) s) from hm]
      rfl
    rw [hidv, hcv]
    rfl
  have hinrval : (mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) inrMap s) w₂ =
      (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from
        ((0 : TangentSpace I x), w₂)) := by
    have hc : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun _ : ℝ => x) s := mdifferentiableAt_const
    have hid : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t) s := mdifferentiableAt_id
    have hprod := mfderiv_prodMk (hf := hc) (hg := hid)
    change (mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (fun t : ℝ => (x, t)) s) w₂ =
      (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from ((0 : TangentSpace I x), w₂))
    rw [hprod]
    change (((mfderiv 𝓘(ℝ, ℝ) I (fun _ : ℝ => x) s) w₂),
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t) s) w₂)) =
      (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from ((0 : TangentSpace I x), w₂))
    have hcv : (mfderiv 𝓘(ℝ, ℝ) I (fun _ : ℝ => x) s) w₂ = (0 : TangentSpace I x) := by
      have hm := mfderiv_const (𝕜 := ℝ) (I := 𝓘(ℝ, ℝ)) (I' := I) (x := s) (c := x)
      rw [show (mfderiv 𝓘(ℝ, ℝ) I (fun _ : ℝ => x) s) =
          (0 : TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ] TangentSpace I x) from hm]
      rfl
    have hidv : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => t) s) w₂ = w₂ := by
      change ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (@id ℝ) s) w₂) = w₂
      rw [show (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (@id ℝ) s) =
          ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, ℝ) s) by
        exact mfderiv_id (𝕜 := ℝ) (E := ℝ) (H := ℝ) (I := 𝓘(ℝ, ℝ)) (M := ℝ) (x := s)]
      rfl
    rw [hcv, hidv]
    rfl
  have hsplit : w = (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from
      (((mfderiv I (I.prod 𝓘(ℝ, ℝ)) inlMap x) w₁) +
        ((mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) inrMap s) w₂))) := by
    rw [hinlval, hinrval]
    change w = (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from
      ((w₁, (0 : TangentSpace 𝓘(ℝ, ℝ) s)) + ((0 : TangentSpace I x), w₂)))
    rw [hw₁, hw₂]
    simp
  have hmain : (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Fp (x, s)) w =
      (mfderiv I 𝓘(ℝ, ℝ) (fun y : M => F y s) x) w₁ +
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => F x t) s) w₂ := by
    rw [hsplit]
    change (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Fp (x, s))
        ((mfderiv I (I.prod 𝓘(ℝ, ℝ)) inlMap x) w₁ +
          (mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) inrMap s) w₂) =
      (mfderiv I 𝓘(ℝ, ℝ) (fun y : M => F y s) x) w₁ +
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => F x t) s) w₂
    rw [map_add]
    have hinlcomp : (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Fp (x, s))
        ((mfderiv I (I.prod 𝓘(ℝ, ℝ)) inlMap x) w₁) =
        (mfderiv I 𝓘(ℝ, ℝ) (fun y : M => F y s) x) w₁ := by
      have hc := mfderiv_comp (x := x) (g := Fp) (f := inlMap) (hg := hFp) (hf := hinl)
      have hfun : (Fp ∘ inlMap) = (fun y : M => F y s) := by
        funext y
        dsimp [Fp, inlMap]
      rw [hfun] at hc
      change ((mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Fp (x, s)).comp
          (mfderiv I (I.prod 𝓘(ℝ, ℝ)) inlMap x)) w₁ = (mfderiv I 𝓘(ℝ, ℝ) (fun y : M => F y s) x) w₁
      rw [← hc]
    have hinrcomp : (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Fp (x, s))
        ((mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) inrMap s) w₂) =
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => F x t) s) w₂ := by
      have hc := mfderiv_comp (x := s) (g := Fp) (f := inrMap) (hg := hFp) (hf := hinr)
      have hfun : (Fp ∘ inrMap) = (fun t : ℝ => F x t) := by
        funext t
        dsimp [Fp, inrMap]
      rw [hfun] at hc
      change ((mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Fp (x, s)).comp
          (mfderiv 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) inrMap s)) w₂ =
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => F x t) s) w₂
      rw [← hc]
    rw [hinlcomp, hinrcomp]
  have hge : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => F x t) s) =
      fderiv ℝ (fun t : ℝ => F x t) s := by
    exact (mfderiv_eq_fderiv (𝕜 := ℝ) (E := ℝ) (E' := ℝ)
      (f := fun t : ℝ => F x t) (x := s))
  rw [hmain]
  change (NormedSpace.fromTangentSpace (F x s))
      ((mfderiv I 𝓘(ℝ, ℝ) (fun y : M => F y s) x) w₁ +
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => F x t) s) w₂) =
      (NormedSpace.fromTangentSpace (F x s)) ((mfderiv I 𝓘(ℝ, ℝ) (fun y : M => F y s) x) w₁) +
        ((fderiv ℝ (fun t : ℝ => F x t) s) 1) *
          (NormedSpace.fromTangentSpace (s : ℝ)) w₂
  have hsum : (NormedSpace.fromTangentSpace (F x s))
      ((mfderiv I 𝓘(ℝ, ℝ) (fun y : M => F y s) x) w₁ +
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => F x t) s) w₂) =
      (NormedSpace.fromTangentSpace (F x s)) ((mfderiv I 𝓘(ℝ, ℝ) (fun y : M => F y s) x) w₁) +
        (NormedSpace.fromTangentSpace (F x s)) ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => F x t) s) w₂) := by
    rw [map_add]
  rw [hsum]
  have hlin : (NormedSpace.fromTangentSpace (F x s))
      ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => F x t) s) w₂) =
      ((fderiv ℝ (fun t : ℝ => F x t) s) 1) * (NormedSpace.fromTangentSpace (s : ℝ)) w₂ := by
    have hlin' : (fderiv ℝ (fun t : ℝ => F x t) s) (NormedSpace.fromTangentSpace (s : ℝ) w₂) =
        ((fderiv ℝ (fun t : ℝ => F x t) s) 1) * (NormedSpace.fromTangentSpace (s : ℝ) w₂) := by
      calc
        (fderiv ℝ (fun t : ℝ => F x t) s) (NormedSpace.fromTangentSpace (s : ℝ) w₂)
            = (fderiv ℝ (fun t : ℝ => F x t) s)
                ((NormedSpace.fromTangentSpace (s : ℝ) w₂) • (1 : ℝ)) := by
              rw [smul_eq_mul, mul_one]
        _ = (NormedSpace.fromTangentSpace (s : ℝ) w₂) •
            ((fderiv ℝ (fun t : ℝ => F x t) s) 1) := by
              rw [← (fderiv ℝ (fun t : ℝ => F x t) s).map_smul]
        _ = ((fderiv ℝ (fun t : ℝ => F x t) s) 1) * (NormedSpace.fromTangentSpace (s : ℝ) w₂) := by
              rw [smul_eq_mul, mul_comm]
    change (NormedSpace.fromTangentSpace (F x s))
        ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => F x t) s)
          (show TangentSpace 𝓘(ℝ, ℝ) s from (NormedSpace.fromTangentSpace (s : ℝ) w₂))) =
      ((fderiv ℝ (fun t : ℝ => F x t) s) 1) * (NormedSpace.fromTangentSpace (s : ℝ)) w₂
    rw [hge]
    exact hlin'
  rw [hlin]

private theorem suspension_level_equation
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (F : M → ℝ → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2)) (x : M) (s : ℝ)
    (v : TangentSpace I x) (ρs : ℝ) :
    (NormedSpace.fromTangentSpace (F x s))
      ((mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : M × ℝ => F q.1 q.2) (x, s))
        (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (v, ρs))) =
      (NormedSpace.fromTangentSpace (F x s)) ((mfderiv I 𝓘(ℝ, ℝ) (fun y : M => F y s) x) v) +
        ((fderiv ℝ (fun t : ℝ => F x t) s) 1) * ρs := by
  have hd := family_mfderiv_decomp (I := I) F hF x s
    (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (v, ρs))
  have hw₁ : (mfderiv (I.prod 𝓘(ℝ, ℝ)) I (fun q : M × ℝ => q.1) (x, s))
      (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (v, ρs)) = v := by
    have hm := mfderiv_fst (𝕜 := ℝ) (E := MorseModel (m + 1)) (H := H) (I := I) (M := M)
      (E' := ℝ) (H' := ℝ) (I' := 𝓘(ℝ, ℝ)) (M' := ℝ) (x := (x, s))
    rw [show (mfderiv (I.prod 𝓘(ℝ, ℝ)) I Prod.fst (x, s)) =
        ContinuousLinearMap.fst ℝ (TangentSpace I x) (TangentSpace 𝓘(ℝ, ℝ) s) from hm]
    change (ContinuousLinearMap.fst ℝ (TangentSpace I x) (TangentSpace 𝓘(ℝ, ℝ) s))
        (show TangentSpace I x × TangentSpace 𝓘(ℝ, ℝ) s from
          (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (v, ρs))) = v
    change v = v
    rfl
  have hw₂ : (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : M × ℝ => q.2) (x, s))
      (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (v, ρs)) =
      (show TangentSpace 𝓘(ℝ, ℝ) s from ρs) := by
    have hm := mfderiv_snd (𝕜 := ℝ) (E := MorseModel (m + 1)) (H := H) (I := I) (M := M)
      (E' := ℝ) (H' := ℝ) (I' := 𝓘(ℝ, ℝ)) (M' := ℝ) (x := (x, s))
    rw [show (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.snd (x, s)) =
        ContinuousLinearMap.snd ℝ (TangentSpace I x) (TangentSpace 𝓘(ℝ, ℝ) s) from hm]
    change (ContinuousLinearMap.snd ℝ (TangentSpace I x) (TangentSpace 𝓘(ℝ, ℝ) s))
        (show TangentSpace I x × TangentSpace 𝓘(ℝ, ℝ) s from
          (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (v, ρs))) =
      (show TangentSpace 𝓘(ℝ, ℝ) s from ρs)
    change (show TangentSpace 𝓘(ℝ, ℝ) s from ρs) = (show TangentSpace 𝓘(ℝ, ℝ) s from ρs)
    rfl
  have hw₂' : (NormedSpace.fromTangentSpace (s : ℝ))
      ((mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : M × ℝ => q.2) (x, s))
        (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (x, s) from (v, ρs))) = ρs := by
    rw [hw₂]
    rfl
  rw [hd, hw₁, hw₂']


private theorem familyChartRep_coefficient_contMDiffOn
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] (F : M → ℝ → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2)) (x₀ : M) (i : Fin (m + 1)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : M × ℝ => (fderiv ℝ (fun q : (MorseModel (m + 1)) × ℝ =>
        F ((extChartAt I x₀).symm q.1) q.2) ((extChartAt I x₀) p.1, p.2))
          (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ (Pi.single i (1 : ℝ))))
      ((extChartAt I x₀).source ×ˢ Set.univ) := by
  have ha' : ContMDiffOn 𝓘(ℝ, (MorseModel (m + 1)) × ℝ) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (MorseModel (m + 1)) × ℝ =>
        (fderiv ℝ (fun q' : (MorseModel (m + 1)) × ℝ => F ((extChartAt I x₀).symm q'.1) q'.2) q)
          (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ (Pi.single i (1 : ℝ))))
      ((extChartAt I x₀).target ×ˢ Set.univ) := by
    exact (contMDiffOn_iff_contDiffOn (𝕜 := ℝ) (E := (MorseModel (m + 1)) × ℝ) (E' := ℝ)
      (f := fun q : (MorseModel (m + 1)) × ℝ =>
        (fderiv ℝ (fun q' : (MorseModel (m + 1)) × ℝ => F ((extChartAt I x₀).symm q'.1) q'.2) q)
          (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ (Pi.single i (1 : ℝ))))
      (s := (extChartAt I x₀).target ×ˢ Set.univ) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))).2
      (familyChartRep_fderiv_apply_contDiffOn (I := I) F hF x₀ i)
  have hφ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, (MorseModel (m + 1)) × ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : M × ℝ => ((extChartAt I x₀) p.1, p.2))
      ((extChartAt I x₀).source ×ˢ Set.univ) := by
    have hc := contMDiffOn_extChartAt (I := I.prod 𝓘(ℝ, ℝ)) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))
      (x := (x₀, (0 : ℝ)))
    simpa [extChartAt_prod, extChartAt_source (I := I) (x := x₀)] using hc
  exact (ha'.comp hφ (by intro p hp; exact ⟨(extChartAt I x₀).map_source hp.1, trivial⟩)).congr
    (by intro p hp; rfl)

private theorem familyTangentSection_contMDiffWithinAt_section_iff
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
    {W : (x : M) → (s : ℝ) → TangentSpace I x} {a : Set (M × ℝ)} {p : M × ℝ}
    (ha : a ⊆ (extChartAt I p.1).source ×ˢ Set.univ) :
    ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (⟨q.1, W q.1 q.2⟩ : TangentBundle I M)) a p ↔
      ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
          ⟨q.1, W q.1 q.2⟩).2) a p := by
  let σ : M × ℝ → TangentBundle I M := fun q => ⟨q.1, W q.1 q.2⟩
  have hσp : (σ p).proj = p.1 := rfl
  have hπ : ContinuousWithinAt (fun q : M × ℝ => (σ q).proj) a p := by
    have hfst : ContinuousWithinAt (fun q : M × ℝ => q.1) a p := continuousWithinAt_fst
    simpa [σ] using hfst
  constructor
  · intro h
    have hcont := h.continuousWithinAt
    have hcont' := (FiberBundle.continuousWithinAt_totalSpace (f := σ) (s := a) (x₀ := p)).1 hcont
    have h2 : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, (MorseModel (m + 1)) × MorseModel (m + 1))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (extChartAt (I.prod 𝓘(ℝ, MorseModel (m + 1))) (σ p) ∘ σ) a p :=
      (contMDiffWithinAt_iff_target (I := I.prod 𝓘(ℝ, ℝ)) (I' := I.prod 𝓘(ℝ, MorseModel (m + 1)))
        (f := σ) (s := a) (x := p) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))).1 h |>.2
    have h2' : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, (MorseModel (m + 1)) × MorseModel (m + 1))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => ((extChartAt I p.1)
          ((trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).1),
          (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).2)) a p := by
      simpa [FiberBundle.extChartAt, hσp, Function.comp_def, PartialEquiv.trans_apply,
        PartialEquiv.prod_coe, PartialEquiv.refl_coe] using h2
    have hfiber : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).2) a p := by
      have hsplit := (contMDiffWithinAt_prod_module_iff (𝕜 := ℝ) (I := I.prod 𝓘(ℝ, ℝ))
        (F₁ := MorseModel (m + 1)) (F₂ := MorseModel (m + 1))
        (f := fun q : M × ℝ => ((extChartAt I p.1)
          ((trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).1),
          (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).2))
        (s := a) (x := p) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))).1 h2'
      simpa using hsplit.2
    simpa [σ, hσp] using (contMDiffWithinAt_iff_target (I := I.prod 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, MorseModel (m + 1)))
      (f := fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).2)
      (s := a) (x := p) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))).mpr
      ⟨hcont'.2, hfiber⟩
  · intro hfib
    have hcontfib : ContinuousWithinAt (fun q : M × ℝ =>
        (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).2) a p :=
      hfib.continuousWithinAt
    have hcont : ContinuousWithinAt σ a p := by
      exact (FiberBundle.continuousWithinAt_totalSpace (f := σ) (s := a) (x₀ := p)).2
        ⟨hπ, by simpa [hσp] using hcontfib⟩
    have hfst : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) I (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun q : M × ℝ => q.1) a p :=
      contMDiffWithinAt_fst
    have hxsrc : p.1 ∈ (chartAt H p.1).source := mem_chart_source (H := H) (M := M) p.1
    have hchart : ContMDiffAt I 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞) (extChartAt I p.1) p.1 :=
      contMDiffAt_extChartAt' (I := I) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (x := p.1) hxsrc
    have hfirst : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (extChartAt I p.1) q.1) a p :=
      hchart.contMDiffWithinAt.comp p hfst (by intro q hq; exact (ha hq).1)
    have hfirst' : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (extChartAt I p.1)
          ((trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).1)) a p := by
      have heq : (fun q : M × ℝ => (extChartAt I p.1)
          ((trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).1)) =ᶠ[nhdsWithin p a]
          (fun q : M × ℝ => (extChartAt I p.1) q.1) := by
        filter_upwards [self_mem_nhdsWithin] with q hq
        have hmem : q.1 ∈ (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1).baseSet := by
          have hq' := ha hq
          simpa [← extChartAt_source] using hq'.1
        rw [(trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1).coe_fst' hmem]
      exact hfirst.congr_of_eventuallyEq heq (by
        exact congrArg (extChartAt I p.1)
          ((trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1).coe_fst'
            (mem_baseSet_trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1)))
    have hpair : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, (MorseModel (m + 1)) × MorseModel (m + 1))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => ((extChartAt I p.1)
          ((trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).1),
          (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).2)) a p := by
      exact (contMDiffWithinAt_prod_module_iff (𝕜 := ℝ) (I := I.prod 𝓘(ℝ, ℝ))
        (F₁ := MorseModel (m + 1)) (F₂ := MorseModel (m + 1))
        (f := fun q : M × ℝ => ((extChartAt I p.1)
          ((trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).1),
          (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).2))
        (s := a) (x := p) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))).2 ⟨hfirst', hfib⟩
    have hσcmd : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1)))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) σ a p := by
      simpa [FiberBundle.extChartAt, hσp, Function.comp_def, PartialEquiv.trans_apply,
        PartialEquiv.prod_coe, PartialEquiv.refl_coe] using
        (contMDiffWithinAt_iff_target (I := I.prod 𝓘(ℝ, ℝ)) (I' := I.prod 𝓘(ℝ, MorseModel (m + 1)))
          (f := σ) (s := a) (x := p) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))).mpr ⟨hcont, hpair⟩
    exact hσcmd

private theorem familyTangentSection_contMDiffWithinAt_section_iff'
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
    {W : (x : M) → (s : ℝ) → TangentSpace I x} {a : Set (M × ℝ)} {p : M × ℝ}
    (x₀ : M) (hp : p.1 ∈ (trivializationAt (MorseModel (m + 1)) (TangentSpace I) x₀).baseSet) :
    ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
          ⟨q.1, W q.1 q.2⟩).2) a p ↔
      ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) x₀
          ⟨q.1, W q.1 q.2⟩).2) a p := by
  let e : Bundle.Trivialization (MorseModel (m + 1))
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    trivializationAt (MorseModel (m + 1)) (TangentSpace I) x₀
  let σ : M × ℝ → TangentBundle I M := fun q => ⟨q.1, W q.1 q.2⟩
  have hproj : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (Bundle.TotalSpace.proj ∘ σ) a p := by
    have hfst : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => q.1) a p := by
      exact contMDiffWithinAt_fst
    simpa [σ] using hfst
  have he₁ : σ p ∈ (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1).source := by
    dsimp [σ]
    simp
  have he₂ : σ p ∈ e.source := by
    dsimp [σ]
    rw [e.mem_source]
    simpa using hp
  have hiff := Bundle.Trivialization.contMDiffWithinAt_snd_comp_iff₂ (f := σ)
    (hp := hproj) (he := he₁) (he' := he₂)
  change ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1 (σ q)).2) a p ↔
    ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (e (σ q)).2) a p
  exact hiff

private theorem familyTangentSection_smul_section
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
    {W : (x : M) → (s : ℝ) → TangentSpace I x} {ψ : M × ℝ → ℝ} {u : Set (M × ℝ)} {p : M × ℝ}
    (hψ : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) ψ u p)
    (hW : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, W q.1 q.2⟩ : TangentBundle I M)) u p) :
    ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, ψ q • W q.1 q.2⟩ : TangentBundle I M)) u p := by
  let u' : Set (M × ℝ) := u ∩ ((extChartAt I p.1).source ×ˢ Set.univ)
  have hu'sub : u' ⊆ (extChartAt I p.1).source ×ˢ Set.univ := by
    intro q hq
    exact hq.2
  have hψ' : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) ψ u' p :=
    hψ.mono (by intro q hq; exact hq.1)
  have hW' : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1)))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, W q.1 q.2⟩ : TangentBundle I M)) u' p :=
    hW.mono (by intro q hq; exact hq.1)
  have hiff := familyTangentSection_contMDiffWithinAt_section_iff (I := I)
    (W := W) (a := u') (p := p) hu'sub
  have hfib : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
        ⟨q.1, W q.1 q.2⟩).2) u' p :=
    hiff.mp hW'
  have hsmul : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => ψ q • (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
        ⟨q.1, W q.1 q.2⟩).2) u' p :=
    hψ'.smul hfib
  let e : Bundle.Trivialization (MorseModel (m + 1))
      (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
    trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
  have hlin : (fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
      ⟨q.1, ψ q • W q.1 q.2⟩).2) =ᶠ[nhdsWithin p u']
      (fun q : M × ℝ => ψ q • (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
        ⟨q.1, W q.1 q.2⟩).2) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    have hqbase : q.1 ∈ e.baseSet := by
      have hq' := hu'sub hq
      simpa [← extChartAt_source] using hq'.1
    exact (e.linear ℝ hqbase).2 (ψ q) (W q.1 q.2)
  have hsmul' : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
        ⟨q.1, ψ q • W q.1 q.2⟩).2) u' p :=
    hsmul.congr_of_eventuallyEq hlin (by
      exact (e.linear ℝ (mem_baseSet_trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1)).2
        (ψ p) (W p.1 p.2))
  have hiff' := familyTangentSection_contMDiffWithinAt_section_iff (I := I)
    (W := fun x s => ψ (x, s) • W x s) (a := u') (p := p) hu'sub
  have hgoal : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1)))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, ψ q • W q.1 q.2⟩ : TangentBundle I M)) u' p :=
    hiff'.mpr hsmul'
  exact hgoal.mono_of_mem_nhdsWithin (by
    have hC : (extChartAt I p.1).source ×ˢ Set.univ ∈ nhds p :=
      (IsOpen.prod (isOpen_extChartAt_source p.1) isOpen_univ).mem_nhds
        ⟨mem_extChartAt_source p.1, trivial⟩
    exact inter_mem_nhdsWithin u hC)

private theorem familyTangentSection_finsum_of_locallyFinite
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
    {ι : Type*} {t : ι → (x : M) → (s : ℝ) → TangentSpace I x}
    (ht : LocallyFinite (fun i : ι => {q : M × ℝ | t i q.1 q.2 ≠ 0}))
    (ht' : ∀ i, ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, t i q.1 q.2⟩ : TangentBundle I M))) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, ∑ᶠ i, t i q.1 q.2⟩ : TangentBundle I M)) := by
  intro p
  rcases ht p with ⟨U, hUp, hfin⟩
  let F : Finset ι := hfin.toFinset
  have hFcover : ∀ i, i ∉ F → t i p.1 p.2 = 0 := by
    intro i hi
    by_contra hnot
    have hmem : ((fun i : ι => {q : M × ℝ | t i q.1 q.2 ≠ 0}) i ∩ U).Nonempty :=
      ⟨p, ⟨by simpa [Function.support] using hnot, mem_of_mem_nhds hUp⟩⟩
    exact hi (by simpa [F] using hfin.mem_toFinset.mpr hmem)
  have hsup : Function.support (fun i : ι => t i p.1 p.2) ⊆ F := by
    intro i hi
    by_contra hnot
    exact False.elim (hi (hFcover i hnot))
  have hsum : (∑ᶠ i, t i p.1 p.2) = ∑ i ∈ F, t i p.1 p.2 := by
    exact finsum_eq_sum_of_support_subset (fun i : ι => t i p.1 p.2) hsup
  have hsumOn : ∀ q ∈ U, (∑ᶠ i, t i q.1 q.2) = ∑ i ∈ F, t i q.1 q.2 := by
    intro q hq
    have hsup' : Function.support (fun i : ι => t i q.1 q.2) ⊆ F := by
      intro i hi
      by_contra hnot
      have hmem : ((fun i : ι => {q : M × ℝ | t i q.1 q.2 ≠ 0}) i ∩ U).Nonempty :=
        ⟨q, ⟨hi, hq⟩⟩
      exact hnot (by simpa [F] using hfin.mem_toFinset.mpr hmem)
    exact finsum_eq_sum_of_support_subset (fun i : ι => t i q.1 q.2) hsup'
  let U' : Set (M × ℝ) := U ∩ ((extChartAt I p.1).source ×ˢ Set.univ)
  have hU'sub : U' ⊆ (extChartAt I p.1).source ×ˢ Set.univ := by
    intro q hq
    exact hq.2
  have hpU' : p ∈ U' := ⟨mem_of_mem_nhds hUp, ⟨mem_extChartAt_source p.1, trivial⟩⟩
  have hfinite : ∀ q ∈ U', (∑ᶠ i, t i q.1 q.2) = ∑ i ∈ F, t i q.1 q.2 := by
    intro q hq
    exact hsumOn q hq.1
  have hfibsum : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
        ⟨q.1, ∑ i ∈ F, t i q.1 q.2⟩).2) U' p := by
    let e : Bundle.Trivialization (MorseModel (m + 1))
        (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
      trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
    have hlin : ∀ q ∈ U', (e ⟨q.1, ∑ i ∈ F, t i q.1 q.2⟩).2 =
        ∑ i ∈ F, (e ⟨q.1, t i q.1 q.2⟩).2 := by
      intro q hq
      have hqbase : q.1 ∈ e.baseSet := by
        have hq' := hU'sub hq
        simpa [← extChartAt_source] using hq'.1
      let L : TangentSpace I q.1 →+ MorseModel (m + 1) :=
        { toFun := fun v => (e ⟨q.1, v⟩).2
          map_zero' := (e.linear ℝ hqbase).map_zero
          map_add' := (e.linear ℝ hqbase).1 }
      classical
      induction F using Finset.induction_on with
      | empty =>
        simpa only [Finset.sum_empty] using (e.linear ℝ hqbase).map_zero
      | insert i s hi ih =>
        calc
          (e ⟨q.1, ∑ j ∈ insert i s, t j q.1 q.2⟩).2
              = (e ⟨q.1, t i q.1 q.2 + ∑ j ∈ s, t j q.1 q.2⟩).2 := by
                rw [Finset.sum_insert hi]
          _ = (e ⟨q.1, t i q.1 q.2⟩).2 + (e ⟨q.1, ∑ j ∈ s, t j q.1 q.2⟩).2 := by
                exact (e.linear ℝ hqbase).1 (t i q.1 q.2) (∑ j ∈ s, t j q.1 q.2)
          _ = (e ⟨q.1, t i q.1 q.2⟩).2 + ∑ j ∈ s, (e ⟨q.1, t j q.1 q.2⟩).2 := by
                rw [ih]
          _ = ∑ j ∈ insert i s, (e ⟨q.1, t j q.1 q.2⟩).2 := by
                rw [Finset.sum_insert hi]
    have hfibs : ∀ i, ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (e ⟨q.1, t i q.1 q.2⟩).2) U' p := by
      intro i
      have hiff := familyTangentSection_contMDiffWithinAt_section_iff (I := I)
        (W := t i) (a := U') (p := p) hU'sub
      exact hiff.mp (((ht' i) p).contMDiffWithinAt (s := U'))
    have hsum' : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => ∑ i ∈ F, (e ⟨q.1, t i q.1 q.2⟩).2) U' p := by
      classical
      induction F using Finset.induction_on with
      | empty =>
        simpa only [Finset.sum_empty] using
          (contMDiffWithinAt_const : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1))
            (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : M × ℝ => (0 : MorseModel (m + 1))) U' p)
      | insert i s hi ih =>
        simpa only [Finset.sum_insert hi] using (hfibs i).add ih
    exact hsum'.congr_of_eventuallyEq (by
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact hlin q hq) (hlin p hpU')
  have hiffs := familyTangentSection_contMDiffWithinAt_section_iff (I := I)
    (W := fun x s => ∑ᶠ i, t i x s) (a := U') (p := p) hU'sub
  have hsec : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1)))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, ∑ᶠ i, t i q.1 q.2⟩ : TangentBundle I M)) U' p := by
    apply hiffs.mpr
    refine hfibsum.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q hq
      rw [hfinite q hq]
    · change (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
        ⟨p.1, ∑ᶠ i, t i p.1 p.2⟩).2 = (trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
          ⟨p.1, ∑ i ∈ F, t i p.1 p.2⟩).2
      rw [hsum]
  exact hsec.mono_of_mem_nhdsWithin (by
    have hC : (extChartAt I p.1).source ×ˢ Set.univ ∈ nhds p :=
      (IsOpen.prod (isOpen_extChartAt_source p.1) isOpen_univ).mem_nhds
        ⟨mem_extChartAt_source p.1, trivial⟩
    simpa [U', nhdsWithin_univ] using (Filter.inter_mem hUp hC))

private theorem familyTangentSection_smul_of_tsupport
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
    {W : (x : M) → (s : ℝ) → TangentSpace I x} {ψ : M × ℝ → ℝ} {u : Set (M × ℝ)}
    (hψ : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) ψ u)
    (ht : IsOpen u) (ht' : tsupport ψ ⊆ u)
    (hW : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, W q.1 q.2⟩ : TangentBundle I M)) u) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, ψ q • W q.1 q.2⟩ : TangentBundle I M)) := by
  apply contMDiff_of_contMDiffOn_union_of_isOpen
  · intro p hp
    exact familyTangentSection_smul_section (I := I) (W := W) (ψ := ψ) (u := u) (p := p)
      (hψ p hp) (hW p hp)
  · intro p hp
    have hzero : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1)))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (⟨q.1, (0 : TangentSpace I q.1)⟩ : TangentBundle I M))
        (tsupport ψ)ᶜ p := by
      let u' : Set (M × ℝ) := (tsupport ψ)ᶜ ∩ ((extChartAt I p.1).source ×ˢ Set.univ)
      have hu'sub : u' ⊆ (extChartAt I p.1).source ×ˢ Set.univ := by
        intro q hq
        exact hq.2
      have hp' : p ∈ u' := ⟨hp, ⟨mem_extChartAt_source p.1, trivial⟩⟩
      have hiff := familyTangentSection_contMDiffWithinAt_section_iff (I := I)
        (W := fun _ _ => (0 : TangentSpace I _)) (a := u') (p := p) hu'sub
      let e : Bundle.Trivialization (MorseModel (m + 1))
          (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
        trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1
      have hfib : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1))
          (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : M × ℝ => (e ⟨q.1, (0 : TangentSpace I q.1)⟩).2) u' p := by
        have hconst : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1))
            (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : M × ℝ => (0 : MorseModel (m + 1))) u' p :=
          contMDiffWithinAt_const
        have heq : (fun q : M × ℝ => (e ⟨q.1, (0 : TangentSpace I q.1)⟩).2) =ᶠ[nhdsWithin p u']
            (fun _ : M × ℝ => (0 : MorseModel (m + 1))) := by
          filter_upwards [self_mem_nhdsWithin] with q hq
          have hqbase : q.1 ∈ e.baseSet := by
            have hq' := hu'sub hq
            simpa [← extChartAt_source] using hq'.1
          exact (e.linear ℝ hqbase).map_zero
        exact hconst.congr_of_eventuallyEq heq (by
          exact (e.linear ℝ (mem_baseSet_trivializationAt (MorseModel (m + 1)) (TangentSpace I) p.1)).map_zero)
      have hgoal : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1)))
          (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : M × ℝ => (⟨q.1, (0 : TangentSpace I q.1)⟩ : TangentBundle I M)) u' p :=
        hiff.mpr hfib
      exact hgoal.mono_of_mem_nhdsWithin (by
        have hC : (extChartAt I p.1).source ×ˢ Set.univ ∈ nhds p :=
          (IsOpen.prod (isOpen_extChartAt_source p.1) isOpen_univ).mem_nhds
            ⟨mem_extChartAt_source p.1, trivial⟩
        exact inter_mem_nhdsWithin (tsupport ψ)ᶜ hC)
    exact hzero.congr_of_eventuallyEq (by
      filter_upwards [self_mem_nhdsWithin] with q hq
      simp [image_eq_zero_of_notMem_tsupport hq]) (by
      simp [image_eq_zero_of_notMem_tsupport hp])
  · exact Set.compl_subset_iff_union.mp <| Set.compl_subset_compl.mpr ht'
  · exact ht
  · exact (isClosed_tsupport ψ).isOpen_compl

private theorem suspensionSection_contMDiff
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
    {W : (x : M) → (s : ℝ) → TangentSpace I x}
    (hW : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, W q.1 q.2⟩ : TangentBundle I M))) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, (MorseModel (m + 1)) × ℝ))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q, (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) q from
        (W q.1 q.2, (1 : ℝ)))⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
  have hψ : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.2, (1 : TangentSpace 𝓘(ℝ, ℝ) q.2)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    have hone : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => (⟨t, (1 : TangentSpace 𝓘(ℝ, ℝ) t)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
      intro t₀
      rw [Bundle.contMDiffAt_section]
      simpa using (contMDiffAt_const (c := (1 : ℝ)))
    exact hone.comp contMDiff_snd
  have hpair : ContMDiff (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, MorseModel (m + 1))).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ =>
        ((⟨q.1, W q.1 q.2⟩ : TangentBundle I M),
          (⟨q.2, (1 : TangentSpace 𝓘(ℝ, ℝ) q.2)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))) :=
    hW.prodMk hψ
  have hsymm : ContMDiff ((I.prod 𝓘(ℝ, MorseModel (m + 1))).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, (MorseModel (m + 1)) × ℝ))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      ((equivTangentBundleProd I M 𝓘(ℝ, ℝ) ℝ).symm) := by
    haveI : IsManifold I (1 : WithTop ℕ∞) M := IsManifold.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
    haveI : IsManifold 𝓘(ℝ, ℝ) (1 : WithTop ℕ∞) ℝ := IsManifold.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
    exact contMDiff_equivTangentBundleProd_symm
  exact hsymm.comp hpair

private theorem suspensionSection_smul_contMDiff
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
    {W : (x : M) → (s : ℝ) → TangentSpace I x} {α : M × ℝ → ℝ}
    (hW : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, W q.1 q.2⟩ : TangentBundle I M)))
    (hα : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) α) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, (MorseModel (m + 1)) × ℝ))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q, (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) q from
        (α q • W q.1 q.2, α q))⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
  have hαW : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, α q • W q.1 q.2⟩ : TangentBundle I M)) := by
    exact familyTangentSection_smul_of_tsupport (I := I) (W := W) (ψ := α) (u := Set.univ)
      (by intro q hq; exact hα q) isOpen_univ (by simp) (by intro q hq; exact hW q)
  have hψ : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.2, (α q : TangentSpace 𝓘(ℝ, ℝ) q.2)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    intro q₀
    rw [Bundle.contMDiffAt_totalSpace]
    constructor
    · exact contMDiffAt_snd
    · have heq : ∀ q : M × ℝ, (trivializationAt ℝ (TangentSpace 𝓘(ℝ, ℝ)) q₀.2
          (⟨q.2, (α q : TangentSpace 𝓘(ℝ, ℝ) q.2)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)).2 = α q := by
        intro q
        simp
      exact (hα q₀).congr_of_eventuallyEq (Filter.Eventually.of_forall heq)
  have hpair : ContMDiff (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, MorseModel (m + 1))).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ =>
        ((⟨q.1, α q • W q.1 q.2⟩ : TangentBundle I M),
          (⟨q.2, (α q : TangentSpace 𝓘(ℝ, ℝ) q.2)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))) :=
    hαW.prodMk hψ
  have hsymm : ContMDiff ((I.prod 𝓘(ℝ, MorseModel (m + 1))).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, (MorseModel (m + 1)) × ℝ))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      ((equivTangentBundleProd I M 𝓘(ℝ, ℝ) ℝ).symm) := by
    haveI : IsManifold I (1 : WithTop ℕ∞) M := IsManifold.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
    haveI : IsManifold 𝓘(ℝ, ℝ) (1 : WithTop ℕ∞) ℝ := IsManifold.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
    exact contMDiff_equivTangentBundleProd_symm
  exact hsymm.comp hpair

private theorem suspensionSection_smul2_contMDiff
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
    {W : (x : M) → (s : ℝ) → TangentSpace I x} {α : M × ℝ → ℝ} {β : M × ℝ → ℝ}
    (hW : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, W q.1 q.2⟩ : TangentBundle I M)))
    (hα : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) α)
    (hβ : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) β) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, (MorseModel (m + 1)) × ℝ))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q, (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) q from
        (α q • W q.1 q.2, β q))⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
  have hαW : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, α q • W q.1 q.2⟩ : TangentBundle I M)) := by
    exact familyTangentSection_smul_of_tsupport (I := I) (W := W) (ψ := α) (u := Set.univ)
      (by intro q hq; exact hα q) isOpen_univ (by simp) (by intro q hq; exact hW q)
  have hψ : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.2, (β q : TangentSpace 𝓘(ℝ, ℝ) q.2)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    intro q₀
    rw [Bundle.contMDiffAt_totalSpace]
    constructor
    · exact contMDiffAt_snd
    · have heq : ∀ q : M × ℝ, (trivializationAt ℝ (TangentSpace 𝓘(ℝ, ℝ)) q₀.2
          (⟨q.2, (β q : TangentSpace 𝓘(ℝ, ℝ) q.2)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)).2 = β q := by
        intro q
        simp
      exact (hβ q₀).congr_of_eventuallyEq (Filter.Eventually.of_forall heq)
  have hpair : ContMDiff (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, MorseModel (m + 1))).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ =>
        ((⟨q.1, α q • W q.1 q.2⟩ : TangentBundle I M),
          (⟨q.2, (β q : TangentSpace 𝓘(ℝ, ℝ) q.2)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))) :=
    hαW.prodMk hψ
  have hsymm : ContMDiff ((I.prod 𝓘(ℝ, MorseModel (m + 1))).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, (MorseModel (m + 1)) × ℝ))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      ((equivTangentBundleProd I M 𝓘(ℝ, ℝ) ℝ).symm) := by
    haveI : IsManifold I (1 : WithTop ℕ∞) M := IsManifold.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
    haveI : IsManifold 𝓘(ℝ, ℝ) (1 : WithTop ℕ∞) ℝ := IsManifold.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)
    exact contMDiff_equivTangentBundleProd_symm
  exact hsymm.comp hpair

private lemma eq_self_of_deriv_one_on_unit
    {φ : ℝ → ℝ} (hφ : DifferentiableOn ℝ φ Set.univ)
    (hφ' : ∀ t : ℝ, t ∈ Set.Icc 0 1 → deriv φ t = 1) (h0 : φ 0 = 0) : φ 1 = 1 := by
  have hcont : ContinuousOn φ (Set.uIcc 0 1) := by
    exact (hφ.mono (by intro u hu; trivial)).continuousOn
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt φ 1 x := by
    intro x hx
    have hx' : x ∈ Set.Icc 0 1 := ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    exact ((hφ x trivial).differentiableAt Filter.univ_mem).hasDerivAt.congr_deriv (hφ' x hx')
  have hderivOn : ∀ x ∈ Set.uIcc (0 : ℝ) 1, deriv φ x = 1 := by
    intro x hx
    exact hφ' x (by simpa using hx)
  have hcontDeriv : ContinuousOn (deriv φ) (Set.uIcc (0 : ℝ) 1) := by
    exact continuousOn_const.congr (by intro x hx; exact hderivOn x hx)
  have hint : IntervalIntegrable (deriv φ) MeasureTheory.volume 0 1 := by
    exact hcontDeriv.intervalIntegrable
  have hderiv' : ∀ x ∈ Set.uIcc (0 : ℝ) 1, DifferentiableAt ℝ φ x := by
    intro x hx
    exact (hφ x trivial).differentiableAt Filter.univ_mem
  have hmain := intervalIntegral.integral_deriv_eq_sub hderiv' hint
  have hint1 : (∫ x in (0 : ℝ)..1, (1 : ℝ)) = 1 := by
    rw [intervalIntegral.integral_const]
    norm_num
  have heqint : (∫ x in (0 : ℝ)..1, deriv φ x) = (∫ x in (0 : ℝ)..1, (1 : ℝ)) := by
    exact intervalIntegral.integral_congr (by intro x hx; exact hderivOn x hx)
  have hval : φ 1 - φ 0 = 1 := by
    rw [heqint] at hmain
    rw [hint1] at hmain
    exact hmain.symm
  linarith

private lemma sublevel_const_of_deriv_eq_zero_ge'
    {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f Set.univ) {L : ℝ} (_hL : 0 < L) {a : ℝ}
    (hfa : f a ∈ Set.Ioo (-L) L)
    (hderiv : ∀ t : ℝ, f t ∈ Set.Icc (-L) L → deriv f t = 0)
    {t₁ : ℝ} (ht₁ : a ≤ t₁) (hgt : f a < f t₁) : f t₁ = f a := by
  let S : Set ℝ := {u : ℝ | u ∈ Set.Icc a t₁ ∧ f a < f u}
  have hSne : S.Nonempty := ⟨t₁, ⟨⟨ht₁, le_rfl⟩, hgt⟩⟩
  have hSbdd : BddBelow S := ⟨a, by intro u hu; exact hu.1.1⟩
  let t₀ : ℝ := sInf S
  have ht₀a : a ≤ t₀ := le_csInf hSne (by intro u hu; exact hu.1.1)
  have ht₀t₁ : t₀ ≤ t₁ := csInf_le hSbdd ⟨⟨ht₁, le_rfl⟩, hgt⟩
  have hcont : ContinuousAt f t₀ := (hf.continuousOn t₀ trivial).continuousAt Filter.univ_mem
  have hf₀_ge : f a ≤ f t₀ := by
    have hcl : t₀ ∈ closure S := csInf_mem_closure hSne hSbdd
    have hright : ∀ᶠ u in nhdsWithin t₀ S, f a ≤ f u := by
      rw [Filter.eventually_iff_exists_mem]
      exact ⟨S ∩ Set.univ, inter_mem_nhdsWithin S Filter.univ_mem, by
        intro u hu
        exact le_of_lt (hu.1).2⟩
    have htend : Tendsto f (nhdsWithin t₀ S) (nhds (f t₀)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    haveI : (nhdsWithin t₀ S).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
    exact ge_of_tendsto htend hright
  have hsub : ∀ u : ℝ, a < u → u < t₀ → f u ≤ f a := by
    intro u hu₁ hu₂
    by_cases huS : u ∈ S
    · have : t₀ ≤ u := csInf_le hSbdd huS
      linarith
    · have hucc : u ∈ Set.Icc a t₁ := ⟨le_of_lt hu₁, le_of_lt (lt_of_lt_of_le hu₂ ht₀t₁)⟩
      exact le_of_not_gt (fun hfu => huS ⟨hucc, hfu⟩)
  have hf₀_le : f t₀ ≤ f a := by
    by_cases ht₀a' : a = t₀
    · simp [ht₀a']
    · have hlt₀ : a < t₀ := lt_of_le_of_ne ht₀a (by intro h; exact ht₀a' h)
      have hleft : ∀ᶠ u in nhdsWithin t₀ (Set.Iio t₀), f u ≤ f a := by
        have hU : {u : ℝ | a < u} ∈ nhds t₀ := isOpen_Ioi.mem_nhds hlt₀
        rw [Filter.eventually_iff_exists_mem]
        exact ⟨Set.Iio t₀ ∩ {u : ℝ | a < u}, inter_mem_nhdsWithin (Set.Iio t₀) hU, by
          intro u hu
          exact hsub u hu.2 hu.1⟩
      have htend : Tendsto f (nhdsWithin t₀ (Set.Iio t₀)) (nhds (f t₀)) :=
        hcont.tendsto.mono_left nhdsWithin_le_nhds
      have ht₀cl : t₀ ∈ closure (Set.Iio t₀) := by
        rw [closure_Iio]
        change t₀ ≤ t₀
        exact le_rfl
      haveI : (nhdsWithin t₀ (Set.Iio t₀)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp ht₀cl
      exact le_of_tendsto htend hleft
  have hf₀ : f t₀ = f a := le_antisymm hf₀_le hf₀_ge
  have hinner : f t₀ ∈ Set.Ioo (-L) L := by
    rw [hf₀]
    exact hfa
  have hloc : ∀ᶠ u in nhds t₀, f u = f t₀ := by
    have hopen : {u : ℝ | f u ∈ Set.Ioo (-L) L} ∈ nhds t₀ :=
      hcont.preimage_mem_nhds (isOpen_Ioo.mem_nhds hinner)
    rcases Metric.mem_nhds_iff.mp hopen with ⟨δ, hδ, hball⟩
    have hdOn : ∀ v ∈ Metric.ball t₀ δ, deriv f v = 0 := by
      intro v hv
      exact hderiv v ⟨le_of_lt (hball hv).1, le_of_lt (hball hv).2⟩
    filter_upwards [Metric.ball_mem_nhds t₀ hδ] with u hu
    exact (isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (hf.mono (by intro v hv; trivial))
      (by
        intro v hv
        exact hdOn v (by simpa [Real.ball_eq_Ioo] using hv))
      (by simpa [Real.ball_eq_Ioo] using hu)
      (by simpa [Real.ball_eq_Ioo] using (Metric.mem_ball_self (α := ℝ) (ε := δ) hδ : t₀ ∈ Metric.ball t₀ δ)))
  rcases hloc.exists_mem with ⟨U, hU, hball⟩
  rcases Metric.mem_nhds_iff.mp hU with ⟨δ, hδ, hballU⟩
  have hSarb : ∃ u ∈ S, u < t₀ + δ := by
    by_contra hnot
    have hleall : ∀ u ∈ S, t₀ + δ ≤ u := by
      intro u hu
      exact le_of_not_gt (fun h => hnot ⟨u, hu, h⟩)
    have : t₀ + δ ≤ sInf S := le_csInf hSne hleall
    linarith
  rcases hSarb with ⟨u, huS, hult⟩
  have hδlt : u > t₀ := by
    by_contra hnot'
    have hu_le : u ≤ t₀ := le_of_not_gt hnot'
    have ht₀_le : t₀ ≤ u := csInf_le hSbdd huS
    have hu_eq : u = t₀ := le_antisymm hu_le ht₀_le
    have hfua : f a < f u := huS.2
    have hcontr : f a < f a := by
      calc
        f a = f t₀ := hf₀.symm
        _ = f u := by rw [hu_eq]
        _ > f a := hfua
    exact (lt_irrefl (f a)) hcontr
  have hu_near : u ∈ Metric.ball t₀ δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    rw [abs_of_pos (sub_pos.mpr hδlt)]
    linarith [hult]
  have hfu : f u = f t₀ := hball u (hballU hu_near)
  have hfua' : f a < f u := huS.2
  have hcontr : f a < f a := by
    calc
      f a = f t₀ := hf₀.symm
      _ = f u := hfu.symm
      _ > f a := hfua'
  exact False.elim (lt_irrefl (f a) hcontr)

private lemma sublevel_const_of_deriv_eq_zero_ge
    {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f Set.univ) {L : ℝ} (hL : 0 < L) {a : ℝ}
    (hfa : f a ∈ Set.Ioo (-L) L)
    (hderiv : ∀ t : ℝ, f t ∈ Set.Icc (-L) L → deriv f t = 0) :
    ∀ t : ℝ, a ≤ t → f t = f a := by
  intro t₁ ht₁
  by_cases heq : f t₁ = f a
  · exact heq
  · rcases lt_or_gt_of_ne heq with hlt | hgt
    · let g : ℝ → ℝ := fun u => -f u
      have hg : DifferentiableOn ℝ g Set.univ := by
        intro u hu
        exact hf u hu |>.neg
      have hgfa : g a ∈ Set.Ioo (-L) L := by
        change -f a ∈ Set.Ioo (-L) L
        constructor
        · exact neg_lt_neg hfa.2
        · simpa using neg_lt_neg hfa.1
      have hgderiv : ∀ u : ℝ, g u ∈ Set.Icc (-L) L → deriv g u = 0 := by
        intro u hu
        have h0 : deriv g u = -deriv f u := by
          dsimp [g]
          simpa only [neg_one_smul] using (deriv_const_smul (c := (-1 : ℝ)) (f := f) (x := u) (hf := (hf u trivial).differentiableAt Filter.univ_mem))
        rw [h0]
        have hu' : f u ∈ Set.Icc (-L) L := by
          dsimp [g] at hu
          constructor
          · simpa using (neg_le_neg hu.2)
          · simpa using (neg_le_neg hu.1)
        rw [hderiv u hu']
        simp
      have hgmain := sublevel_const_of_deriv_eq_zero_ge' hg hL hgfa hgderiv ht₁ (by
        dsimp [g]
        exact neg_lt_neg hlt)
      have hgval : g t₁ = -f t₁ := rfl
      have hgvala : g a = -f a := rfl
      rw [hgval, hgvala] at hgmain
      exact neg_inj.mp hgmain
    · exact sublevel_const_of_deriv_eq_zero_ge' hf hL hfa hderiv ht₁ hgt

private lemma sublevel_const_of_deriv_eq_zero_on_interval
    {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f Set.univ) {L : ℝ} (hL : 0 < L) {a : ℝ}
    (hfa : f a ∈ Set.Ioo (-L) L)
    (hderiv : ∀ t : ℝ, f t ∈ Set.Icc (-L) L → deriv f t = 0) :
    ∀ t : ℝ, f t = f a := by
  intro t₁
  by_cases ht₁a : a ≤ t₁
  · exact sublevel_const_of_deriv_eq_zero_ge hf hL hfa hderiv t₁ ht₁a
  · have hlt : t₁ < a := lt_of_not_ge ht₁a
    let g : ℝ → ℝ := fun u => f (a - u)
    have hg : DifferentiableOn ℝ g Set.univ := by
      intro u hu
      dsimp [g]
      refine DifferentiableWithinAt.comp (𝕜 := ℝ) (E := ℝ) (F := ℝ) (G := ℝ)
        (f := fun u : ℝ => a - u) (g := f) (s := Set.univ) (t := Set.univ) (x := u) ?_ ?_ ?_
      · exact hf (a - u) trivial
      · exact DifferentiableWithinAt.sub (f := fun _ : ℝ => a) (g := fun u : ℝ => u)
          (differentiableWithinAt_const (c := a) (x := u)) differentiableWithinAt_id
      · intro y hy; trivial
    have hgfa : g 0 ∈ Set.Ioo (-L) L := by
      simpa [g] using hfa
    have hgderiv : ∀ u : ℝ, g u ∈ Set.Icc (-L) L → deriv g u = 0 := by
      intro u hu
      have h0 : deriv g u = -deriv f (a - u) := by
        dsimp [g]
        have hin : DifferentiableAt ℝ (fun u : ℝ => a - u) u := by fun_prop
        have hout : DifferentiableAt ℝ f (a - u) :=
          (hf (a - u) trivial).differentiableAt Filter.univ_mem
        change deriv (f ∘ (fun u : ℝ => a - u)) u = -deriv f (a - u)
        rw [deriv_comp u hout hin]
        · have hd : deriv (fun u : ℝ => a - u) u = -1 := by
            simpa [deriv_id] using (deriv_const_sub (c := a) (f := fun u : ℝ => u) (x := u))
          rw [hd]
          simp
      rw [h0]
      rw [hderiv (a - u) hu]
      simp
    have hle : 0 ≤ a - t₁ := by linarith
    have hmain := sublevel_const_of_deriv_eq_zero_ge hg hL hgfa hgderiv (a - t₁) hle
    have hgval : g (a - t₁) = f t₁ := by
      dsimp [g]
      ring_nf
    rw [hgval] at hmain
    simpa [g] using hmain

private lemma sublevel_const_of_deriv_eq_zero_on_unit'
    {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f Set.univ) {L : ℝ} (_hL : 0 < L)
    (hf0 : f 0 ∈ Set.Ioo (-L) L)
    (hderiv : ∀ t : ℝ, t ∈ Set.Icc 0 1 → f t ∈ Set.Icc (-L) L → deriv f t = 0)
    {t₁ : ℝ} (ht₁ : t₁ ∈ Set.Icc 0 1) (hgt : f 0 < f t₁) : f t₁ = f 0 := by
  let S : Set ℝ := {u : ℝ | u ∈ Set.Icc 0 t₁ ∧ f 0 < f u}
  have hSne : S.Nonempty := ⟨t₁, ⟨⟨ht₁.1, le_rfl⟩, hgt⟩⟩
  have hSbdd : BddBelow S := ⟨0, by intro u hu; exact hu.1.1⟩
  let t₀ : ℝ := sInf S
  have ht₀₀ : 0 ≤ t₀ := le_csInf hSne (by intro u hu; exact hu.1.1)
  have ht₀t₁ : t₀ ≤ t₁ := csInf_le hSbdd ⟨⟨ht₁.1, le_rfl⟩, hgt⟩
  have ht₀₁ : t₀ ≤ 1 := le_trans ht₀t₁ ht₁.2
  have hcont : ContinuousAt f t₀ := (hf.continuousOn t₀ trivial).continuousAt Filter.univ_mem
  have hf₀_ge : f 0 ≤ f t₀ := by
    have hcl : t₀ ∈ closure S := csInf_mem_closure hSne hSbdd
    have hright : ∀ᶠ u in nhdsWithin t₀ S, f 0 ≤ f u := by
      rw [Filter.eventually_iff_exists_mem]
      exact ⟨S ∩ Set.univ, inter_mem_nhdsWithin S Filter.univ_mem, by
        intro u hu
        exact le_of_lt (hu.1).2⟩
    have htend : Tendsto f (nhdsWithin t₀ S) (nhds (f t₀)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    haveI : (nhdsWithin t₀ S).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
    exact ge_of_tendsto htend hright
  have hsub : ∀ u : ℝ, 0 < u → u < t₀ → f u ≤ f 0 := by
    intro u hu₁ hu₂
    by_cases huS : u ∈ S
    · have : t₀ ≤ u := csInf_le hSbdd huS
      linarith
    · have hucc : u ∈ Set.Icc 0 t₁ := ⟨le_of_lt hu₁, le_of_lt (lt_of_lt_of_le hu₂ ht₀t₁)⟩
      exact le_of_not_gt (fun hfu => huS ⟨hucc, hfu⟩)
  have hf₀_le : f t₀ ≤ f 0 := by
    by_cases ht₀₀' : 0 = t₀
    · simp [ht₀₀']
    · have hlt₀ : 0 < t₀ := lt_of_le_of_ne ht₀₀ (by intro h; exact ht₀₀' h)
      have hleft : ∀ᶠ u in nhdsWithin t₀ (Set.Iio t₀), f u ≤ f 0 := by
        have hU : {u : ℝ | 0 < u} ∈ nhds t₀ := isOpen_Ioi.mem_nhds hlt₀
        rw [Filter.eventually_iff_exists_mem]
        exact ⟨Set.Iio t₀ ∩ {u : ℝ | 0 < u}, inter_mem_nhdsWithin (Set.Iio t₀) hU, by
          intro u hu
          exact hsub u hu.2 hu.1⟩
      have htend : Tendsto f (nhdsWithin t₀ (Set.Iio t₀)) (nhds (f t₀)) :=
        hcont.tendsto.mono_left nhdsWithin_le_nhds
      have ht₀cl : t₀ ∈ closure (Set.Iio t₀) := by
        rw [closure_Iio]
        change t₀ ≤ t₀
        exact le_rfl
      haveI : (nhdsWithin t₀ (Set.Iio t₀)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp ht₀cl
      exact le_of_tendsto htend hleft
  have hf₀ : f t₀ = f 0 := le_antisymm hf₀_le hf₀_ge
  have hinner : f t₀ ∈ Set.Ioo (-L) L := by
    rw [hf₀]
    exact hf0
  have ht₀lt : t₀ < 1 := by
    by_cases ht₁lt : t₁ < 1
    · exact lt_of_le_of_lt ht₀t₁ ht₁lt
    · have ht₁eq : t₁ = 1 := le_antisymm ht₁.2 (le_of_not_gt ht₁lt)
      have hf1 : f 0 < f 1 := by simpa [ht₁eq] using hgt
      have hcont1 : ContinuousAt f 1 := (hf.continuousOn 1 trivial).continuousAt Filter.univ_mem
      have hev : {u : ℝ | f 0 < f u} ∈ nhds 1 :=
        hcont1.preimage_mem_nhds (isOpen_Ioi.mem_nhds hf1)
      rcases Metric.mem_nhds_iff.mp hev with ⟨δ, hδ, hball⟩
      let δ₀ : ℝ := min δ 1
      have hδ₀ : 0 < δ₀ := by exact lt_min hδ (by norm_num)
      have hballδ : Metric.ball (1 : ℝ) δ₀ ⊆ Metric.ball (1 : ℝ) δ := Metric.ball_subset_ball (min_le_left δ 1)
      have hmem : 1 - δ₀ / 2 ∈ Set.Icc 0 1 := by
        constructor <;> linarith [hδ₀, min_le_right δ 1]
      have hfmem : f 0 < f (1 - δ₀ / 2) := hball (hballδ (by
        rw [Metric.mem_ball, Real.dist_eq]
        rw [abs_of_neg (by linarith [hδ₀] : 1 - δ₀ / 2 - 1 < 0)]
        linarith))
      have hS' : 1 - δ₀ / 2 ∈ S := ⟨by simpa [ht₁eq] using hmem, hfmem⟩
      have : t₀ ≤ 1 - δ₀ / 2 := csInf_le hSbdd hS'
      linarith [hδ₀]
  have hloc : ∀ᶠ u in nhdsWithin t₀ (Set.Icc 0 1), f u = f t₀ := by
    have hopen : {u : ℝ | f u ∈ Set.Ioo (-L) L} ∈ nhds t₀ :=
      hcont.preimage_mem_nhds (isOpen_Ioo.mem_nhds hinner)
    rcases Metric.mem_nhds_iff.mp hopen with ⟨δ, hδ, hball⟩
    by_cases ht₀z : t₀ = 0
    · rw [ht₀z]
      let δ₀ : ℝ := min δ 1
      have hδ₀ : 0 < δ₀ := lt_min hδ (by norm_num)
      have hdOn : ∀ v : ℝ, v ∈ Set.Ioo 0 δ₀ → deriv f v = 0 := by
        intro v hv
        have hvi : v ∈ Set.Icc 0 1 := ⟨le_of_lt hv.1, le_of_lt (lt_of_lt_of_le hv.2 (by linarith [hδ₀, min_le_right δ 1]))⟩
        have hvball : v ∈ Metric.ball 0 δ := by
          rw [Metric.mem_ball, Real.dist_eq]
          rw [sub_zero, abs_of_pos hv.1]
          linarith [hv.2, hδ₀, min_le_left δ 1]
        have hfv : f v ∈ Set.Ioo (-L) L := by
          simpa [ht₀z] using hball (by simpa [ht₀z] using hvball)
        exact hderiv v hvi ⟨le_of_lt hfv.1, le_of_lt hfv.2⟩
      have hconstOn : ∀ v : ℝ, v ∈ Set.Ioo 0 δ₀ → f v = f (δ₀ / 2) := by
        intro v hv
        exact (isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
          (hf.mono (by intro w hw; trivial))
          (by intro w hw; exact hdOn w hw)
          hv (by constructor <;> linarith [hδ₀]))
      have hc0 : f (δ₀ / 2) = f 0 := by
        have hseq : Tendsto (fun n : ℕ => f (δ₀ / 2 / (n + 1))) atTop (nhds (f 0)) := by
          have harg : Tendsto (fun n : ℕ => δ₀ / 2 / (n + 1)) atTop (nhds 0) := by
            have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhds 0) :=
              tendsto_one_div_add_atTop_nhds_zero_nat
            have hconst : Tendsto (fun _ : ℕ => (δ₀ / 2 : ℝ)) atTop (nhds (δ₀ / 2)) :=
              tendsto_const_nhds
            simpa [div_eq_mul_inv, mul_assoc] using (hconst.mul hinv)
          exact (hf.continuousOn 0 trivial).continuousAt Filter.univ_mem |>.tendsto.comp harg
        have hmain : ∀ᶠ n : ℕ in atTop, f (δ₀ / 2 / (n + 1)) = f (δ₀ / 2) := by
          exact Filter.Eventually.of_forall (fun n => hconstOn (δ₀ / 2 / (n + 1)) (by
            constructor
            · positivity
            · have hle1 : (1 : ℝ) / (n + 1) ≤ 1 := by
                rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n + 1))]
                have hn0 : (0 : ℝ) ≤ n := by positivity
                nlinarith
              have hle2 : (δ₀ / 2) * (((n : ℝ) + 1)⁻¹) ≤ δ₀ / 2 := by
                simpa [one_div] using (mul_le_mul_of_nonneg_left hle1 (by positivity : (0 : ℝ) ≤ δ₀ / 2))
              have hlt2 : δ₀ / 2 < δ₀ := by linarith [hδ₀]
              rw [div_eq_mul_inv]
              exact lt_of_le_of_lt hle2 hlt2))
        have heqev : (fun _ : ℕ => f (δ₀ / 2)) =ᶠ[atTop] (fun n : ℕ => f (δ₀ / 2 / (n + 1))) := by
          exact Filter.EventuallyEq.symm hmain
        have htendc : Tendsto (fun n : ℕ => f (δ₀ / 2 / (n + 1))) atTop (nhds (f (δ₀ / 2))) := by
          exact tendsto_const_nhds.congr' heqev
        exact (tendsto_nhds_unique hseq htendc).symm
      rw [Filter.eventually_iff_exists_mem]
      refine ⟨Set.Icc 0 1 ∩ Metric.ball 0 δ₀,
        inter_mem_nhdsWithin (Set.Icc (0 : ℝ) 1) (Metric.ball_mem_nhds (0 : ℝ) hδ₀), ?_⟩
      intro u hu
      rcases hu with ⟨huc, hub⟩
      have huI : u ∈ Set.Icc 0 δ₀ := ⟨huc.1, le_of_lt (by rw [Real.ball_eq_Ioo] at hub; simpa using hub.2)⟩
      by_cases huz : u = 0
      · simp [huz]
      · have hupos : 0 < u := lt_of_le_of_ne huI.1 (by intro h; exact huz h.symm)
        have hultδ : u < δ₀ := by rw [Real.ball_eq_Ioo] at hub; simpa using hub.2
        rw [hconstOn u (by constructor <;> linarith [hupos, hultδ]), hc0]
    · have ht₀pos : 0 < t₀ := lt_of_le_of_ne ht₀₀ (by intro h; exact ht₀z h.symm)
      let δ₀ : ℝ := min δ (min t₀ (1 - t₀))
      have hδ₀ : 0 < δ₀ := by
        exact lt_min hδ (lt_min ht₀pos (by linarith [ht₀lt]))
      have hdOn : ∀ v : ℝ, v ∈ Metric.ball t₀ δ₀ → deriv f v = 0 := by
        intro v hv
        have hvi : v ∈ Set.Icc 0 1 := by
          rw [Real.ball_eq_Ioo] at hv
          constructor
          · linarith [hv.1, min_le_right δ (min t₀ (1 - t₀)), min_le_left t₀ (1 - t₀)]
          · linarith [hv.2, min_le_right δ (min t₀ (1 - t₀)), min_le_right t₀ (1 - t₀)]
        have hvball : v ∈ Metric.ball t₀ δ := by
          exact Metric.ball_subset_ball (min_le_left δ (min t₀ (1 - t₀))) hv
        exact hderiv v hvi ⟨le_of_lt (hball hvball).1, le_of_lt (hball hvball).2⟩
      rw [Filter.eventually_iff_exists_mem]
      refine ⟨Metric.ball t₀ δ₀,
        (mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨Metric.ball t₀ δ₀,
          Metric.ball_mem_nhds t₀ hδ₀, by intro u hu; exact hu.1⟩), ?_⟩
      intro u hu
      exact (isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        (hf.mono (by intro v hv; trivial))
        (by intro v hv; exact hdOn v (by simpa [Real.ball_eq_Ioo] using hv))
        (by simpa [Real.ball_eq_Ioo] using hu)
        (by simpa [Real.ball_eq_Ioo] using (Metric.mem_ball_self (α := ℝ) (ε := δ₀) hδ₀ : t₀ ∈ Metric.ball t₀ δ₀)))
  rcases hloc.exists_mem with ⟨U, hU, hball⟩
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hU
  rcases hU with ⟨V, hV, hVsub⟩
  rcases Metric.mem_nhds_iff.mp hV with ⟨δ, hδ, hballV⟩
  have hSarb : ∃ u ∈ S, u < t₀ + δ := by
    by_contra hnot
    have hleall : ∀ u ∈ S, t₀ + δ ≤ u := by
      intro u hu
      exact le_of_not_gt (fun h => hnot ⟨u, hu, h⟩)
    have : t₀ + δ ≤ sInf S := le_csInf hSne hleall
    linarith
  rcases hSarb with ⟨u, huS, hult⟩
  have hδlt : u > t₀ := by
    by_contra hnot'
    have hu_le : u ≤ t₀ := le_of_not_gt hnot'
    have ht₀_le : t₀ ≤ u := csInf_le hSbdd huS
    have hu_eq : u = t₀ := le_antisymm hu_le ht₀_le
    have hfua : f 0 < f u := huS.2
    have hcontr : f 0 < f 0 := by
      calc
        f 0 = f t₀ := hf₀.symm
        _ = f u := by rw [hu_eq]
        _ > f 0 := hfua
    exact (lt_irrefl (f 0)) hcontr
  have hu_near : u ∈ Metric.ball t₀ δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    rw [abs_of_pos (sub_pos.mpr hδlt)]
    linarith [hult]
  have huU : u ∈ U := hVsub ⟨hballV hu_near, ⟨huS.1.1, le_trans huS.1.2 ht₁.2⟩⟩
  have hfu : f u = f t₀ := hball u huU
  have hfua' : f 0 < f u := huS.2
  have hcontr : f 0 < f 0 := by
    calc
      f 0 = f t₀ := hf₀.symm
      _ = f u := hfu.symm
      _ > f 0 := hfua'
  exact False.elim (lt_irrefl (f 0) hcontr)

private lemma sublevel_const_of_deriv_eq_zero_on_unit
    {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f Set.univ) {L : ℝ} (hL : 0 < L)
    (hf0 : f 0 ∈ Set.Ioo (-L) L)
    (hderiv : ∀ t : ℝ, t ∈ Set.Icc 0 1 → f t ∈ Set.Icc (-L) L → deriv f t = 0) :
    ∀ t : ℝ, t ∈ Set.Icc 0 1 → f t = f 0 := by
  intro t₁ ht₁
  by_cases heq : f t₁ = f 0
  · exact heq
  · rcases lt_or_gt_of_ne heq with hlt | hgt
    · let g : ℝ → ℝ := fun u => -f u
      have hg : DifferentiableOn ℝ g Set.univ := by
        intro u hu
        exact hf u hu |>.neg
      have hg0 : g 0 ∈ Set.Ioo (-L) L := by
        change -f 0 ∈ Set.Ioo (-L) L
        constructor
        · exact neg_lt_neg hf0.2
        · simpa using neg_lt_neg hf0.1
      have hgderiv : ∀ t : ℝ, t ∈ Set.Icc 0 1 → g t ∈ Set.Icc (-L) L → deriv g t = 0 := by
        intro t ht hgt
        have h0 : deriv g t = -deriv f t := by
          dsimp [g]
          simpa only [neg_one_smul] using (deriv_const_smul (c := (-1 : ℝ)) (f := f) (x := t)
            (hf := (hf t trivial).differentiableAt Filter.univ_mem))
        rw [h0]
        have hft : f t ∈ Set.Icc (-L) L := by
          dsimp [g] at hgt
          constructor
          · simpa using (neg_le_neg hgt.2)
          · simpa using (neg_le_neg hgt.1)
        rw [hderiv t ht hft]
        simp
      have hmain := sublevel_const_of_deriv_eq_zero_on_unit' hg hL hg0 hgderiv ht₁ (by
        dsimp [g]
        exact neg_lt_neg hlt)
      have hgval : g t₁ = -f t₁ := rfl
      have hgvala : g 0 = -f 0 := rfl
      rw [hgval, hgvala] at hmain
      exact neg_inj.mp hmain
    · exact sublevel_const_of_deriv_eq_zero_on_unit' hf hL hf0 hderiv ht₁ hgt
theorem localUnitSpeedFamilyVectorField_at_noncritical
    (I : ModelWithCorners ℝ (MorseModel (m + 1)) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
    (F : M → ℝ → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2)) {x₀ : M} {s₀ : ℝ}
    (hcrit : ¬ IsCriticalPointAt I (fun x => F x s₀) x₀) :
    ∃ (U : Set (M × ℝ)), (x₀, s₀) ∈ U ∧ IsOpen U ∧
      ∃ W : (x : M) → (s : ℝ) → TangentSpace I x,
        (∀ p ∈ U, (NormedSpace.fromTangentSpace (F p.1 p.2))
          ((mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x p.2) p.1) (W p.1 p.2)) = -1) ∧
        ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : M × ℝ => (⟨q.1, W q.1 q.2⟩ : TangentBundle I M)) U := by
  let g : (MorseModel (m + 1)) × ℝ → ℝ := fun q => F ((extChartAt I x₀).symm q.1) q.2
  have hgOn : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g ((extChartAt I x₀).target ×ˢ Set.univ) := by
    simpa [g] using familyChartRep_contDiffOn (I := I) F hF x₀
  have hfSlice : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun x : M => F x s₀) := by
    have hpair : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun x : M => (x, s₀)) := by
      exact (contMDiff_id (I := I) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞))).prodMk
        (contMDiff_const : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : M => s₀))
    simpa using hF.comp hpair
  have hcritChart : fderiv ℝ (fun y : MorseModel (m + 1) => F ((extChartAt I x₀).symm y) s₀)
      (extChartAt I x₀ x₀) ≠ 0 := by
    have hiff := isCriticalPointAt_iff_chart_fderiv I (fun x : M => F x s₀) hfSlice x₀
    intro hz
    exact hcrit (hiff.2 hz)
  rcases exists_coord_of_fderiv_ne_zero (fun y : MorseModel (m + 1) => F ((extChartAt I x₀).symm y) s₀)
    (extChartAt I x₀ x₀) hcritChart with ⟨i, hi⟩
  have hpi : Pi.single i (1 : ℝ) = fun j : Fin (m + 1) => if j = i then (1 : ℝ) else 0 := by
    ext j
    simp [Pi.single, Function.update_apply]
  let a : M × ℝ → ℝ := fun p =>
    (fderiv ℝ g ((extChartAt I x₀) p.1, p.2))
      (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ (Pi.single i (1 : ℝ)))
  have hcont : ContinuousOn a ((extChartAt I x₀).source ×ˢ Set.univ) := by
    have hcont' : ContinuousOn (fun q : (MorseModel (m + 1)) × ℝ =>
        (fderiv ℝ g q) (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ (Pi.single i (1 : ℝ))))
        ((extChartAt I x₀).target ×ˢ Set.univ) :=
      (familyChartRep_fderiv_apply_contDiffOn (I := I) F hF x₀ i).continuousOn
    have hce : ContinuousOn (fun p : M × ℝ => ((extChartAt I x₀) p.1, p.2))
        ((extChartAt I x₀).source ×ˢ Set.univ) := by
      have hc1 : ContinuousOn (extChartAt I x₀) (extChartAt I x₀).source := by
        simpa [extChartAt_source (I := I) (x := x₀)] using
          (contMDiffOn_extChartAt (I := I) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (x := x₀)).continuousOn
      exact hc1.prodMap continuousOn_id
    exact hcont'.comp hce (by intro p hp; exact ⟨(extChartAt I x₀).map_source hp.1, trivial⟩)
  have hmem₀ : (x₀, s₀) ∈ (extChartAt I x₀).source ×ˢ Set.univ :=
    ⟨mem_extChartAt_source x₀, trivial⟩
  have hne₀ : a (x₀, s₀) ≠ 0 := by
    have hcurry := familyChartRep_fderiv_curry (I := I) F hF x₀ (extChartAt I x₀ x₀) s₀
      ((extChartAt I x₀).map_source (mem_extChartAt_source x₀))
    have heq : (fderiv ℝ (fun y : MorseModel (m + 1) => F ((extChartAt I x₀).symm y) s₀)
        (extChartAt I x₀ x₀)) (Pi.single i (1 : ℝ)) = a (x₀, s₀) := by
      rw [hcurry]
      change ((fderiv ℝ (fun q : (MorseModel (m + 1)) × ℝ => F ((extChartAt I x₀).symm q.1) q.2)
        (extChartAt I x₀ x₀, s₀)).comp (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ))
          (Pi.single i (1 : ℝ)) = (fderiv ℝ (fun q : (MorseModel (m + 1)) × ℝ =>
        F ((extChartAt I x₀).symm q.1) q.2) (extChartAt I x₀ x₀, s₀))
          (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ (Pi.single i (1 : ℝ)))
      rfl
    have hi' : (fderiv ℝ (fun y : MorseModel (m + 1) => F ((extChartAt I x₀).symm y) s₀)
        (extChartAt I x₀ x₀)) (Pi.single i (1 : ℝ)) ≠ 0 := by
      rw [hpi]
      simpa using hi
    rwa [heq] at hi'
  have hV : {p : M × ℝ | a p ≠ 0} ∈ nhds (x₀, s₀) := by
    exact (hcont (x₀, s₀) hmem₀).continuousAt
      ((IsOpen.prod (isOpen_extChartAt_source x₀) isOpen_univ).mem_nhds hmem₀)
      (isOpen_ne.mem_nhds hne₀)
  rcases mem_nhds_iff.mp hV with ⟨V, hVsub, hVopen, hV₀⟩
  let U : Set (M × ℝ) := V ∩ ((extChartAt I x₀).source ×ˢ Set.univ)
  have hUopen : IsOpen U := hVopen.inter (IsOpen.prod (isOpen_extChartAt_source x₀) isOpen_univ)
  let W : (x : M) → (s : ℝ) → TangentSpace I x := fun x s =>
    (mfderivWithin 𝓘(ℝ, MorseModel (m + 1)) I (extChartAt I x₀).symm (range I)
      (extChartAt I x₀ x)) (-(a (x, s))⁻¹ • (Pi.single i (1 : ℝ) : MorseModel (m + 1)))
  refine ⟨U, ⟨hV₀, hmem₀⟩, hUopen, W, ?_, ?_⟩
  · intro p hp
    have hxsrc : p.1 ∈ (extChartAt I x₀).source := hp.2.1
    have hpV : p ∈ V := hp.1
    have ha : a p ≠ 0 := hVsub hpV
    let e : PartialEquiv M (MorseModel (m + 1)) := extChartAt I x₀
    have hepx : e.symm (e p.1) = p.1 := e.left_inv hxsrc
    have hmemxy : (e p.1, p.2) ∈ (extChartAt I x₀).target ×ˢ Set.univ :=
      ⟨e.map_source hxsrc, trivial⟩
    have hmdg := ((hgOn (e p.1, p.2) hmemxy).contDiffAt
      ((IsOpen.prod (isOpen_extChartAt_target x₀) isOpen_univ).mem_nhds hmemxy)).differentiableAt
      (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
    have hmdg' : MDifferentiableAt 𝓘(ℝ, MorseModel (m + 1)) 𝓘(ℝ, ℝ)
        (fun y : MorseModel (m + 1) => g (y, p.2)) (e p.1) := by
      have hpair : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun y : MorseModel (m + 1) => (y, p.2)) (e p.1) := by
        exact (contDiffAt_id.prodMk contDiffAt_const)
      have hgAt : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g (e p.1, p.2) :=
        (hgOn (e p.1, p.2) hmemxy).contDiffAt
          ((IsOpen.prod (isOpen_extChartAt_target x₀) isOpen_univ).mem_nhds hmemxy)
      exact ((ContDiffAt.contMDiffAt (ContDiffAt.comp (𝕜 := ℝ) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (g := g)
        (f := fun y : MorseModel (m + 1) => (y, p.2)) (e p.1) hgAt hpair)).mdifferentiableAt
        (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0))
    have hmdchart := (contMDiffAt_extChartAt' (I := I) (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (x := x₀)
      (by simpa [extChartAt_source] using hxsrc)).mdifferentiableAt (by norm_num)
    have hcomp : mfderiv I 𝓘(ℝ, ℝ) (fun y : M => g (e y, p.2)) p.1 =
        (mfderiv 𝓘(ℝ, MorseModel (m + 1)) 𝓘(ℝ, ℝ) (fun y : MorseModel (m + 1) => g (y, p.2)) (e p.1)).comp
          (mfderiv I 𝓘(ℝ, MorseModel (m + 1)) e p.1) := by
      simpa using (mfderiv_comp (x := p.1) (g := (fun y : MorseModel (m + 1) => g (y, p.2))) (f := e)
        (hg := hmdg') (hf := hmdchart))
    have hfuneq : (fun y : M => F y p.2) =ᶠ[nhds p.1] (fun y : M => g (e y, p.2)) := by
      have hsrcopen : IsOpen e.source := isOpen_extChartAt_source x₀
      exact Filter.eventuallyEq_of_mem (by simpa [e] using (hsrcopen.mem_nhds hxsrc))
        (fun y hy => congrArg (fun z => F z p.2) (e.left_inv hy).symm)
    have heq := Filter.EventuallyEq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ)) hfuneq
    have hge : mfderiv 𝓘(ℝ, MorseModel (m + 1)) 𝓘(ℝ, ℝ) (fun y : MorseModel (m + 1) => g (y, p.2)) (e p.1) =
        fderiv ℝ (fun y : MorseModel (m + 1) => g (y, p.2)) (e p.1) := by
      exact (mfderiv_eq_fderiv (𝕜 := ℝ) (E := MorseModel (m + 1)) (E' := ℝ)
        (f := fun y : MorseModel (m + 1) => g (y, p.2)) (x := e p.1))
    have hcurry := familyChartRep_fderiv_curry (I := I) F hF x₀ (e p.1) p.2 hmemxy.1
    have hslice : fderiv ℝ (fun y : MorseModel (m + 1) => g (y, p.2)) (e p.1) =
        (fderiv ℝ g (e p.1, p.2)).comp (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ) := by
      simpa [g] using hcurry
    have hid := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := x₀)
      (y := e p.1) (by simpa [e] using hmemxy.1)
    have hid' : (mfderiv I 𝓘(ℝ, MorseModel (m + 1)) e p.1) ∘L
        (mfderivWithin 𝓘(ℝ, MorseModel (m + 1)) I e.symm (range I) (e p.1)) =
        ContinuousLinearMap.id _ _ := by
      rw [hepx] at hid
      exact hid
    have hidapply : ∀ w : MorseModel (m + 1),
        (mfderiv I 𝓘(ℝ, MorseModel (m + 1)) e p.1)
          ((mfderivWithin 𝓘(ℝ, MorseModel (m + 1)) I e.symm (range I) (e p.1)) w) = w := by
      intro w
      change (((mfderiv I 𝓘(ℝ, MorseModel (m + 1)) e p.1).comp
        (mfderivWithin 𝓘(ℝ, MorseModel (m + 1)) I e.symm (range I) (e p.1)))) w = w
      rw [hid']
      simp
    have hchartW : ((mfderiv I 𝓘(ℝ, MorseModel (m + 1)) e p.1) : TangentSpace I p.1 →L[ℝ] MorseModel (m + 1))
        (W p.1 p.2) = -(a p)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel (m + 1)) := by
      dsimp [W, a]
      exact hidapply (-(a p)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel (m + 1)))
    have hfinal : (fderiv ℝ (fun y : MorseModel (m + 1) => g (y, p.2)) (e p.1))
        (-(a p)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel (m + 1))) = -1 := by
      rw [hslice]
      rw [ContinuousLinearMap.comp_apply]
      have hinl : ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ
          (-(a p)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel (m + 1))) =
          -(a p)⁻¹ • ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ (Pi.single i (1 : ℝ)) := by
        ext <;> simp
      rw [hinl]
      rw [(fderiv ℝ g (e p.1, p.2)).map_smul]
      rw [smul_eq_mul]
      have haval : (fderiv ℝ g (e p.1, p.2))
          (ContinuousLinearMap.inl ℝ (MorseModel (m + 1)) ℝ (Pi.single i (1 : ℝ))) = a p := by
        rfl
      rw [haval]
      field_simp [ha]
    have hmain : (mfderiv I 𝓘(ℝ, ℝ) (fun y : M => F y p.2) p.1) (W p.1 p.2) = (-1 : ℝ) := by
      rw [heq]
      rw [hcomp]
      change ((mfderiv 𝓘(ℝ, MorseModel (m + 1)) 𝓘(ℝ, ℝ) (fun y : MorseModel (m + 1) => g (y, p.2)) (e p.1) :
          MorseModel (m + 1) →L[ℝ] ℝ))
        (((mfderiv I 𝓘(ℝ, MorseModel (m + 1)) e p.1) : TangentSpace I p.1 →L[ℝ] MorseModel (m + 1))
          (W p.1 p.2)) = (-1 : ℝ)
      rw [hge]
      rw [hchartW]
      exact hfinal
    have hts : (NormedSpace.fromTangentSpace (F p.1 p.2))
        ((mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x p.2) p.1) (W p.1 p.2)) =
        (mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x p.2) p.1) (W p.1 p.2) := by
      rfl
    rw [hts]
    exact hmain
  · intro p hp
    let U' : Set (M × ℝ) := U ∩ ((extChartAt I p.1).source ×ˢ Set.univ)
    have hU'sub : U' ⊆ (extChartAt I p.1).source ×ˢ Set.univ := by
      intro q hq
      exact hq.2
    have hpU' : p ∈ U' := ⟨hp, ⟨mem_extChartAt_source p.1, trivial⟩⟩
    have hiff := familyTangentSection_contMDiffWithinAt_section_iff (I := I)
      (W := W) (a := U') (p := p) hU'sub
    have hiff' := familyTangentSection_contMDiffWithinAt_section_iff' (I := I)
      (W := W) (a := U') (p := p) x₀ (by
        have hp' := hp.2.1
        simpa [extChartAt_source (I := I) (x := x₀)] using hp')
    have hfibVal : ∀ q ∈ U', (trivializationAt (MorseModel (m + 1)) (TangentSpace I) x₀
        ⟨q.1, W q.1 q.2⟩).2 = -(a q)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel (m + 1)) := by
      intro q hq
      have hqsrc : q.1 ∈ (extChartAt I x₀).source := hq.1.2.1
      rw [tangentTrivializationAt_apply I x₀ q.1 hqsrc (W q.1 q.2)]
      dsimp [W, a]
      have hid := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := x₀)
        (y := (extChartAt I x₀) q.1) (by
          simpa using (extChartAt I x₀).map_source hqsrc)
      have hep : (extChartAt I x₀).symm ((extChartAt I x₀) q.1) = q.1 :=
        (extChartAt I x₀).left_inv hqsrc
      have hid'' : (mfderiv I 𝓘(ℝ, MorseModel (m + 1)) (extChartAt I x₀) q.1) ∘L
          (mfderivWithin 𝓘(ℝ, MorseModel (m + 1)) I (extChartAt I x₀).symm (range I)
            ((extChartAt I x₀) q.1)) = ContinuousLinearMap.id _ _ := by
        rw [hep] at hid
        exact hid
      change (((mfderiv I 𝓘(ℝ, MorseModel (m + 1)) (extChartAt I x₀) q.1).comp
        (mfderivWithin 𝓘(ℝ, MorseModel (m + 1)) I (extChartAt I x₀).symm (range I)
          ((extChartAt I x₀) q.1)))) (-(a q)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel (m + 1))) =
        -(a q)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel (m + 1))
      rw [hid'']
      rfl
    have haU : ∀ q ∈ U', a q ≠ 0 := by
      intro q hq
      exact hVsub hq.1.1
    have hcmd : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) a U' p :=
      (familyChartRep_coefficient_contMDiffOn (I := I) F hF x₀ i).mono
        (by intro q hq; exact hq.1.2) p hpU'
    have hinv : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (a q)⁻¹) U' p :=
      hcmd.inv₀ (haU p hpU')
    have hsmul : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => -(a q)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel (m + 1))) U' p := by
      have hconst : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1))
          (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun _ : M × ℝ => (Pi.single i (1 : ℝ) : MorseModel (m + 1))) U' p :=
        contMDiffWithinAt_const
      exact hinv.neg.smul hconst
    have heqfib : (fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) x₀
        ⟨q.1, W q.1 q.2⟩).2) =ᶠ[nhdsWithin p U']
        (fun q : M × ℝ => -(a q)⁻¹ • (Pi.single i (1 : ℝ) : MorseModel (m + 1))) := by
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact hfibVal q hq
    have hfib : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, MorseModel (m + 1)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (trivializationAt (MorseModel (m + 1)) (TangentSpace I) x₀
          ⟨q.1, W q.1 q.2⟩).2) U' p :=
      hsmul.congr_of_eventuallyEq heqfib (hfibVal p hpU')
    have hσU' : ContMDiffWithinAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1)))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun q : M × ℝ => (⟨q.1, W q.1 q.2⟩ : TangentBundle I M)) U' p := by
      rw [hiff, hiff']
      exact hfib
    exact hσU'.mono_of_mem_nhdsWithin (by
      have hC : (extChartAt I p.1).source ×ˢ Set.univ ∈ nhds p :=
        (IsOpen.prod (isOpen_extChartAt_source p.1) isOpen_univ).mem_nhds
          ⟨mem_extChartAt_source p.1, trivial⟩
      exact inter_mem_nhdsWithin U hC)

theorem exists_unitSpeedFamilyVectorField_on_compact
    (I : ModelWithCorners ℝ (MorseModel (m + 1)) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
    (F : M → ℝ → ℝ) (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2)) (K : Set (M × ℝ)) (hcompact : IsCompact K)
    (hregular : ∀ p ∈ K, ¬ IsCriticalPointAt I (fun x => F x p.2) p.1) :
    ∃ V : (x : M) → (s : ℝ) → TangentSpace I x,
      ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => (⟨q.1, V q.1 q.2⟩ : TangentBundle I M)) ∧
      IsCompact (tsupport (fun q : M × ℝ => V q.1 q.2)) ∧
      (∀ p ∈ K, (NormedSpace.fromTangentSpace (F p.1 p.2))
        ((mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x p.2) p.1) (V p.1 p.2)) = -1) ∧
      (∀ q : M × ℝ, -1 ≤ (NormedSpace.fromTangentSpace (F q.1 q.2))
          ((mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x q.2) q.1) (V q.1 q.2)) ∧
        (NormedSpace.fromTangentSpace (F q.1 q.2))
          ((mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x q.2) q.1) (V q.1 q.2)) ≤ 0) := by
  let K : Set (M × ℝ) := K
  have hpts : ∀ x : K, ∃ U : Set (M × ℝ), x.1 ∈ U ∧ IsOpen U ∧
      ∃ W : (x : M) → (s : ℝ) → TangentSpace I x,
        (∀ y ∈ U, (NormedSpace.fromTangentSpace (F y.1 y.2))
          ((mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x y.2) y.1) (W y.1 y.2)) = -1) ∧
        ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : M × ℝ => (⟨y.1, W y.1 y.2⟩ : TangentBundle I M)) U :=
    fun x => localUnitSpeedFamilyVectorField_at_noncritical I F hF (hregular x x.2)
  choose U hUmem hUopen W hWdf hWsec using hpts
  have hKclosed : IsClosed K := hcompact.isClosed
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  rcases exists_open_between_and_isCompact_closure hcompact isOpen_univ (subset_univ K)
    with ⟨W₀, hW₀open, hKW₀, hW₀cl, hW₀compact⟩
  let U' : K → Set (M × ℝ) := fun x => U x ∩ W₀
  have hU'mem : ∀ x : K, x.1 ∈ U' x := fun x => ⟨hUmem x, hKW₀ x.2⟩
  have hU'open : ∀ x : K, IsOpen (U' x) := fun x => (hUopen x).inter hW₀open
  have hcov : K ⊆ ⋃ x : K, U' x := by
    intro y hy
    exact Set.mem_iUnion_of_mem ⟨y, hy⟩ (hU'mem ⟨y, hy⟩)
  rcases SmoothPartitionOfUnity.exists_isSubordinate (I := I.prod 𝓘(ℝ, ℝ)) (s := K) (U := U')
    (hs := hKclosed) (ho := hU'open) (hU := hcov) with ⟨ρ, hρsub⟩
  let V : (x : M) → (s : ℝ) → TangentSpace I x := fun y s =>
    ∑ᶠ x : K, (ρ x (y, s) : ℝ) • (W x y s : TangentSpace I y)
  have hdfsum : ∀ y : M × ℝ,
      (NormedSpace.fromTangentSpace (F y.1 y.2)) ((mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x y.2) y.1) (V y.1 y.2)) =
        -(∑ᶠ x : K, (ρ x y : ℝ)) := by
    intro y
    let L : TangentSpace I y.1 →L[ℝ] ℝ :=
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F y.1 y.2) : TangentSpace 𝓘(ℝ, ℝ) (F y.1 y.2) →L[ℝ] ℝ).comp
        (mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x y.2) y.1)
    have hVdef : (NormedSpace.fromTangentSpace (F y.1 y.2)) ((mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x y.2) y.1) (V y.1 y.2)) = L (V y.1 y.2) := by
      simp [L]
    rw [hVdef]
    have hfinSuppρ : Function.HasFiniteSupport (fun x : K => ρ x y) := by
      have hlf : LocallyFinite (fun x : K => {z : M × ℝ | ρ x z ≠ 0}) := ρ.locallyFinite
      have hlfy := hlf y
      rcases hlfy with ⟨N, hN, hfinN⟩
      have hsub : (Function.support fun x : K => ρ x y) ⊆
          {x : K | ((fun x : K => {z : M × ℝ | ρ x z ≠ 0}) x ∩ N).Nonempty} := by
        intro x hx
        rw [Function.support] at hx
        exact ⟨y, ⟨hx, mem_of_mem_nhds hN⟩⟩
      exact Set.Finite.subset hfinN hsub
    have hfinSupp : Function.HasFiniteSupport (fun x : K => ρ x y • W x y.1 y.2) := by
      exact Set.Finite.subset hfinSuppρ (by intro x hx; exact fun hρ0 => hx (by simp [hρ0]))
    have hlin : L (V y.1 y.2) = ∑ᶠ x : K, L (ρ x y • W x y.1 y.2) := by
      dsimp [V]
      have hmap := (AddMonoidHom.map_finsum (g := (L : TangentSpace I y.1 →+ ℝ)) (hf := hfinSupp))
      simpa using hmap
    rw [hlin]
    have hterm : ∀ x : K, L (ρ x y • W x y.1 y.2) = ρ x y • L (W x y.1 y.2) := by
      intro x
      rw [map_smul]
    have hrew : (∑ᶠ x : K, L (ρ x y • W x y.1 y.2)) = ∑ᶠ x : K, ρ x y • (-1 : ℝ) := by
      apply finsum_congr
      intro x
      rw [hterm x]
      by_cases hyU : y ∈ U' x
      · have hdf := hWdf x y hyU.1
        have hLval : L (W x y.1 y.2) = -1 := by
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
  · have hsummand : ∀ x : K, ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1)))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : M × ℝ => (⟨y.1, ρ x y • W x y.1 y.2⟩ : TangentBundle I M)) := by
      intro x
      have hρOn : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (ρ x : M × ℝ → ℝ) (U' x) := by
        have hc' : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
            (ρ x : M × ℝ → ℝ) Set.univ := by
          simpa using (ρ x).property.contMDiffOn
        exact (hc'.mono (subset_univ _)).of_le le_rfl
      exact familyTangentSection_smul_of_tsupport (I := I) (W := W x) (ψ := ρ x) (u := U' x)
        hρOn (hU'open x) (hρsub x) ((hWsec x).mono (by intro y hy; exact hy.1))
    have hfin : LocallyFinite (fun x : K => {y : M × ℝ | ρ x y • W x y.1 y.2 ≠ 0}) := by
      exact ρ.locallyFinite.subset (fun x => by
        intro y hy
        have hρy : ρ x y ≠ 0 := by
          intro hρ0
          apply hy
          simp [hρ0]
        exact hρy)
    simpa [V] using (familyTangentSection_finsum_of_locallyFinite (I := I)
      (t := fun x : K => fun y s => ρ x (y, s) • W x y s) hfin hsummand)
  · have hmem : ∀ y, y ∈ Function.support (fun q : M × ℝ => V q.1 q.2) → y ∈ ⋃ x : K, tsupport (ρ x) := by
      intro y hy
      by_contra hnot
      have hy' : V y.1 y.2 ≠ 0 := hy
      apply hy'
      have hall : ∀ x : K, (ρ x y : ℝ) • (W x y.1 y.2 : TangentSpace I y.1) = 0 := by
        intro x
        by_contra hx
        apply hnot
        exact Set.mem_iUnion.mpr ⟨x, subset_closure (by
          intro hρ0
          apply hx
          simp [hρ0])⟩
      have hV0 : (∑ᶠ x : K, (ρ x y : ℝ) • (W x y.1 y.2 : TangentSpace I y.1)) = 0 :=
        finsum_eq_zero_of_forall_eq_zero hall
      simpa [V] using hV0
    have hsupp₀ : Function.support (fun q : M × ℝ => V q.1 q.2) ⊆ W₀ := by
      intro y hy
      rcases Set.mem_iUnion.mp (hmem y hy) with ⟨x, hx⟩
      exact (hρsub x hx).2
    have hts : tsupport (fun q : M × ℝ => V q.1 q.2) ⊆ closure W₀ := closure_mono hsupp₀
    exact hW₀compact.of_isClosed_subset (isClosed_tsupport (fun q : M × ℝ => V q.1 q.2)) hts
  · intro y hy
    rw [hdfsum y]
    have hs1 : (∑ᶠ x : K, ρ x y) = 1 := ρ.sum_eq_one hy
    rw [hs1]
  · intro y
    rw [hdfsum y]
    have hnonneg : 0 ≤ ∑ᶠ x : K, (ρ x y : ℝ) := finsum_nonneg (fun x => ρ.nonneg x y)
    have hle1 : (∑ᶠ x : K, (ρ x y : ℝ)) ≤ 1 := ρ.sum_le_one y
    constructor <;> linarith


private lemma snd_range_of_deriv_unit
    {s : ℝ → ℝ} (hs : DifferentiableOn ℝ s Set.univ) (hs0 : s 0 = 0)
    (hs' : ∀ t : ℝ, t ∈ Set.Icc 0 1 → deriv s t ∈ Set.Icc 0 1) :
    ∀ u : ℝ, u ∈ Set.Icc 0 1 → s u ∈ Set.Icc 0 1 := by
  intro u hu
  have hmono : MonotoneOn s (Set.Icc 0 u) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) u)
    · exact hs.continuousOn.mono (by intro x hx; trivial)
    · intro t ht
      have hOn : DifferentiableOn ℝ s (interior (Set.Icc 0 u)) := by
        intro x hx
        exact (hs x trivial).mono (by intro y hy; trivial : interior (Set.Icc 0 u) ⊆ Set.univ)
      exact hOn t ht
    · intro t ht
      exact (hs' t ⟨(interior_subset ht).1, le_trans (interior_subset ht).2 hu.2⟩).1
  have hlo : 0 ≤ s u := by
    have hle := hmono ⟨le_rfl, hu.1⟩ ⟨hu.1, le_rfl⟩ hu.1
    simpa [hs0] using hle
  have hanti : AntitoneOn (fun t : ℝ => s t - t) (Set.Icc 0 u) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) u)
    · exact ((hs.continuousOn.sub continuousOn_id)).mono (by intro x hx; trivial)
    · intro t ht
      have hOn : DifferentiableOn ℝ s (interior (Set.Icc 0 u)) := by
        intro x hx
        exact (hs x trivial).mono (by intro y hy; trivial)
      exact (hOn t ht).sub differentiableAt_id.differentiableWithinAt
    · intro t ht
      have hd : deriv (fun t : ℝ => s t - t) t = deriv s t - 1 := by
        have hsub := deriv_sub ((hs t trivial).differentiableAt Filter.univ_mem) differentiableAt_id
        simpa using hsub
      rw [hd]
      have hb := hs' t ⟨(interior_subset ht).1, le_trans (interior_subset ht).2 hu.2⟩
      linarith [hb.2]
  have hup : s u ≤ u := by
    have hle := hanti ⟨le_rfl, hu.1⟩ ⟨hu.1, le_rfl⟩ hu.1
    dsimp at hle
    have hg0 : s 0 - 0 = 0 := by rw [hs0]; norm_num
    linarith
  exact ⟨hlo, le_trans hup hu.2⟩


private lemma sublevel_const_of_deriv_eq_zero_below
    {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f Set.univ) {L : ℝ} (_hL : 0 < L)
    (hf0 : f 0 ≤ -L) (hderiv : ∀ t : ℝ, t ∈ Set.Icc 0 1 → f t ∈ Set.Icc (-L) L → deriv f t = 0)
    {t₁ : ℝ} (ht₁ : t₁ ∈ Set.Icc 0 1) : f t₁ ≤ -L := by
  by_contra hnot
  have hgt : -L < f t₁ := lt_of_not_ge hnot
  let A : Set ℝ := {t : ℝ | t ∈ Set.Icc 0 t₁ ∧ f t ≤ -L}
  have hAne : A.Nonempty := ⟨0, ⟨⟨le_rfl, ht₁.1⟩, hf0⟩⟩
  have hAbdd : BddAbove A := ⟨t₁, by intro t ht; exact ht.1.2⟩
  let τ : ℝ := sSup A
  have hA0 : 0 ∈ A := ⟨⟨le_rfl, ht₁.1⟩, hf0⟩
  have hτ0 : 0 ≤ τ := le_csSup hAbdd hA0
  have hτt₁ : τ ≤ t₁ := csSup_le hAne (by intro t ht; exact ht.1.2)
  have hcont : ContinuousAt f τ := (hf.continuousOn τ trivial).continuousAt Filter.univ_mem
  have hfτ_le : f τ ≤ -L := by
    have hcl : τ ∈ closure A := csSup_mem_closure hAne hAbdd
    have hright : ∀ᶠ u in nhdsWithin τ A, f u ≤ -L := by
      rw [Filter.eventually_iff_exists_mem]
      exact ⟨A ∩ Set.univ, inter_mem_nhdsWithin A Filter.univ_mem, by intro u hu; exact hu.1.2⟩
    have htend : Tendsto f (nhdsWithin τ A) (nhds (f τ)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    haveI : (nhdsWithin τ A).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
    exact le_of_tendsto htend hright
  have hfτ_ge : -L ≤ f τ := by
    by_cases hτt₁' : τ = t₁
    · rw [hτt₁']
      exact le_of_lt hgt
    · have hlt : τ < t₁ := lt_of_le_of_ne hτt₁ (by intro h; exact hτt₁' h)
      by_contra hle
      have hlt' : f τ < -L := lt_of_not_ge hle
      have hU : {u : ℝ | f u < -L} ∈ nhds τ :=
        hcont.preimage_mem_nhds (isOpen_Iio.mem_nhds hlt')
      rcases Metric.mem_nhds_iff.mp hU with ⟨δ, hδ, hball⟩
      let η : ℝ := min δ ((t₁ - τ) / 2)
      have hη0 : 0 < η := lt_min hδ (div_pos (sub_pos.mpr hlt) (by norm_num))
      have hτη : τ + η / 2 < t₁ := by
        dsimp [η]
        have hmin : min δ ((t₁ - τ) / 2) ≤ (t₁ - τ) / 2 := min_le_right δ ((t₁ - τ) / 2)
        nlinarith [hmin, hlt]
      have hτη' : τ < τ + η / 2 := by linarith [hη0]
      have hmem : τ + η / 2 ∈ A := by
        refine ⟨⟨le_trans hτ0 (le_of_lt hτη'), le_of_lt hτη⟩, ?_⟩
        have hin : τ + η / 2 ∈ Metric.ball τ δ := by
          rw [Metric.mem_ball, Real.dist_eq]
          rw [abs_of_pos (sub_pos.mpr hτη')]
          have hηle : η ≤ δ := min_le_left δ ((t₁ - τ) / 2)
          dsimp [η] at hηle
          nlinarith [hη0, hηle]
        exact le_of_lt (hball hin)
      have hle_sup : τ + η / 2 ≤ τ := le_csSup hAbdd hmem
      have hη2 : 0 < η / 2 := by positivity
      nlinarith [hη2, hle_sup]
  have hfτ : f τ = -L := le_antisymm hfτ_le hfτ_ge
  by_cases hτt₁' : τ = t₁
  · exact hnot (by simpa [hτt₁'] using hfτ_le)
  · have hlt : τ < t₁ := lt_of_le_of_ne hτt₁ (by intro h; exact hτt₁' h)
    have hτL : f τ < L := by
      rw [hfτ]
      have hL' : 0 < L := _hL
      linarith
    have hcontU : {u : ℝ | f u < L} ∈ nhds τ :=
      hcont.preimage_mem_nhds (isOpen_Iio.mem_nhds hτL)
    rcases Metric.mem_nhds_iff.mp hcontU with ⟨δ, hδ, hball⟩
    have hδ' : 0 < min δ ((t₁ - τ) / 2) :=
      lt_min hδ (div_pos (sub_pos.mpr hlt) (by norm_num))
    let ε : ℝ := min δ ((t₁ - τ) / 2)
    have hε0 : 0 < ε := hδ'
    have hτε : τ + ε < t₁ := by
      dsimp [ε]
      have hmin : min δ ((t₁ - τ) / 2) ≤ (t₁ - τ) / 2 := min_le_right δ ((t₁ - τ) / 2)
      nlinarith [hmin, hlt]
    have hfgt : ∀ t : ℝ, t ∈ Set.Ioo τ (τ + ε) → -L < f t := by
      intro t ht
      have htnotA : t ∉ A := by
        intro htA
        have hs : t ≤ τ := le_csSup hAbdd htA
        linarith [ht.1, hs]
      have htI : t ∈ Set.Icc 0 t₁ := ⟨le_trans hτ0 (le_of_lt ht.1), le_of_lt (lt_of_lt_of_le ht.2 (le_of_lt hτε))⟩
      have hnotle : ¬ f t ≤ -L := by
        intro hle
        exact htnotA ⟨htI, hle⟩
      exact lt_of_not_ge hnotle
    have hflt : ∀ t : ℝ, t ∈ Set.Ioo τ (τ + ε) → f t < L := by
      intro t ht
      have hin : t ∈ Metric.ball τ δ := by
        rw [Metric.mem_ball, Real.dist_eq]
        rw [abs_of_pos (sub_pos.mpr ht.1)]
        change t - τ < δ
        have hle' : t - τ < ε := by linarith [ht.2]
        have hεle : ε ≤ δ := by
          dsimp [ε]
          exact min_le_left δ ((t₁ - τ) / 2)
        nlinarith [hεle, hle']
      exact hball hin
    have hcst : ∀ t : ℝ, t ∈ Set.Ioo τ (τ + ε) → f t = f (τ + ε / 2) := by
      intro t ht
      have hc := (isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo (f := f)
        (s := Set.Ioo τ (τ + ε)) (hf.mono (by intro v hv; trivial)))
      have hder : EqOn (deriv f) 0 (Set.Ioo τ (τ + ε)) := by
        intro v hv
        have hstrip : f v ∈ Set.Icc (-L) L := by
          constructor
          · exact le_of_lt (hfgt v hv)
          · exact le_of_lt (hflt v hv)
        exact hderiv v ⟨le_trans hτ0 (le_of_lt hv.1),
          le_trans (le_of_lt (lt_of_lt_of_le hv.2 (le_of_lt hτε))) ht₁.2⟩ hstrip
      exact hc hder (x := t) (y := τ + ε / 2) ht (by constructor <;> linarith [hε0])
    have hclosed : IsClosed {t : ℝ | f t = f (τ + ε / 2)} := by
      exact isClosed_eq (continuousOn_univ.mp hf.continuousOn) continuous_const
    have hmemτ : τ ∈ {t : ℝ | f t = f (τ + ε / 2)} := by
      have hcl : τ ∈ closure (Set.Ioo τ (τ + ε)) := by
        rw [closure_Ioo (by linarith [hε0] : τ ≠ τ + ε)]
        constructor <;> linarith [hε0]
      have hsub : Set.Ioo τ (τ + ε) ⊆ {t : ℝ | f t = f (τ + ε / 2)} := by
        intro u hu
        exact hcst u hu
      exact hclosed.closure_subset (closure_mono hsub hcl)
    have hconst : ∀ t : ℝ, t ∈ Set.Ioo τ (τ + ε) → f t = f τ := by
      intro t ht
      exact (hcst t ht).trans hmemτ.symm
    have hmid : τ + ε / 2 ∈ Set.Ioo τ (τ + ε) := by
      constructor <;> linarith [hε0]
    have hconstmid : f (τ + ε / 2) = f τ := hconst (τ + ε / 2) hmid
    have hgtmid : -L < f (τ + ε / 2) := hfgt (τ + ε / 2) hmid
    rw [hfτ] at hconstmid
    linarith [hgtmid, hconstmid]

private lemma sublevel_sign_agreement_of_no_zero
    {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Icc 0 1))
    (hne : ∀ s : ℝ, s ∈ Set.Icc 0 1 → f s ≠ 0) : (f 0 ≤ 0 ↔ f 1 ≤ 0) := by
  constructor
  · intro hf0
    by_contra hnot
    have hf0lt : f 0 < 0 := lt_of_le_of_ne hf0 (fun h => hne 0 (by norm_num) h)
    have hf1gt : 0 < f 1 := lt_of_not_ge hnot
    have hmem : (0 : ℝ) ∈ Set.uIcc (f 0) (f 1) := by
      dsimp [Set.uIcc]
      constructor
      · exact le_trans (min_le_left (f 0) (f 1)) (le_of_lt hf0lt)
      · exact le_trans (le_of_lt hf1gt) (le_max_right (f 0) (f 1))
    have himg := intermediate_value_uIcc (f := f) (a := 0) (b := 1) (hf := by
      have h01 : Set.uIcc (0 : ℝ) (1 : ℝ) ⊆ Set.Icc (0 : ℝ) (1 : ℝ) := by
        intro x hx
        simpa [Set.uIcc] using hx
      exact hcont.mono h01)
    rcases himg hmem with ⟨c, hc, hcval⟩
    exact hne c (by simpa [Set.uIcc] using hc) hcval
  · intro hf1
    by_contra hnot
    have hf1lt : f 1 < 0 := lt_of_le_of_ne hf1 (fun h => hne 1 (by norm_num) h)
    have hf0gt : 0 < f 0 := lt_of_not_ge hnot
    have hmem : (0 : ℝ) ∈ Set.uIcc (f 1) (f 0) := by
      dsimp [Set.uIcc]
      constructor
      · exact le_trans (min_le_left (f 1) (f 0)) (le_of_lt hf1lt)
      · exact le_trans (le_of_lt hf0gt) (le_max_right (f 1) (f 0))
    have himg := intermediate_value_uIcc (f := f) (a := 1) (b := 0) (hf := by
      have h01 : Set.uIcc (1 : ℝ) (0 : ℝ) ⊆ Set.Icc (0 : ℝ) (1 : ℝ) := by
        intro x hx
        simpa [Set.uIcc] using hx
      exact hcont.mono h01)
    rcases himg hmem with ⟨c, hc, hcval⟩
    exact hne c (by simpa [Set.uIcc] using hc) hcval

private lemma exists_scalar_flow_smooth_cutoff
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H}
    {ρ : M × ℝ → ℝ} {χt : ℝ → ℝ}
    (hρ_sm : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hχt_sm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) χt)
    (hχt_supp : IsCompact (tsupport χt))
    (x : M) (s₀ : ℝ) : ∃ τ : ℝ → ℝ, τ 0 = s₀ ∧
      IsMIntegralCurve (I := 𝓘(ℝ, ℝ)) (M := ℝ) (E := ℝ) (H := ℝ) τ
        (fun s : ℝ => (ρ (x, s) * χt s : TangentSpace 𝓘(ℝ, ℝ) s)) := by
  have hsec : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun s : ℝ => (⟨s, (ρ (x, s) * χt s : TangentSpace 𝓘(ℝ, ℝ) s)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    intro y
    rw [Bundle.contMDiffAt_totalSpace]
    constructor
    · exact contMDiffAt_id
    · have hρx : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s : ℝ => ρ (x, s)) :=
        hρ_sm.comp (contMDiff_const.prodMk contMDiff_id)
      have hf : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun s : ℝ => (ρ (x, s) * χt s : ℝ)) y := by
        exact (hρx.mul hχt_sm).contMDiffAt
      have heq : ∀ s : ℝ, (trivializationAt ℝ (TangentSpace 𝓘(ℝ, ℝ)) y
          (⟨s, (ρ (x, s) * χt s : TangentSpace 𝓘(ℝ, ℝ) s)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)).2 =
          (ρ (x, s) * χt s : ℝ) := by
        intro s
        simp
      exact hf.congr_of_eventuallyEq (Filter.Eventually.of_forall heq)
  have hsupp : IsCompact (tsupport (fun s : ℝ => (ρ (x, s) * χt s : TangentSpace 𝓘(ℝ, ℝ) s))) := by
    have hsub : Function.support (fun s : ℝ => (ρ (x, s) * χt s : TangentSpace 𝓘(ℝ, ℝ) s)) ⊆
        Function.support χt := by
      intro s hs
      dsimp [Function.support] at hs
      by_contra hχt0
      have hχt0' : χt s = 0 := not_not.mp hχt0
      exact hs (by rw [hχt0']; norm_num)
    have hts : tsupport (fun s : ℝ => (ρ (x, s) * χt s : TangentSpace 𝓘(ℝ, ℝ) s)) ⊆ tsupport χt :=
      closure_mono hsub
    exact hχt_supp.of_isClosed_subset (isClosed_tsupport _) hts
  rcases exists_globalIntegralCurve_of_compactSupport (E := ℝ) (I := 𝓘(ℝ, ℝ)) (M := ℝ)
    (v := fun s : ℝ => (ρ (x, s) * χt s : TangentSpace 𝓘(ℝ, ℝ) s)) hsec hsupp s₀ with ⟨τ, hτ0, hτIs⟩
  exact ⟨τ, hτ0, hτIs⟩

private lemma scalarFlow_rho_smoothTransition_bounds
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H}
    {ρ : M × ℝ → ℝ}
    (hρ_sm : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    {x : M} {s₀ : ℝ} (hs₀ : s₀ ∈ Set.Icc 0 1) {σ : ℝ → ℝ} (hσ0 : σ 0 = s₀)
    (hσ : IsMIntegralCurve (I := 𝓘(ℝ, ℝ)) (M := ℝ) (E := ℝ) (H := ℝ) σ
      (fun s : ℝ => (ρ (x, s) * Real.smoothTransition (2 - s) * Real.smoothTransition (s + 1) :
        TangentSpace 𝓘(ℝ, ℝ) s))) :
    ∀ t : ℝ, σ t ∈ Set.Ioo (-1) 2 := by
  let χt : ℝ → ℝ := fun s => Real.smoothTransition (2 - s) * Real.smoothTransition (s + 1)
  let f : ℝ → ℝ := fun s => ρ (x, s) * χt s
  have hχt_m1 : χt (-1) = 0 := by
    dsimp [χt]
    have h2 : Real.smoothTransition ((-1) + 1) = 0 := by
      rw [show (-1 : ℝ) + 1 = 0 by norm_num]
      exact Real.smoothTransition.zero
    rw [h2, mul_zero]
  have hχt_2 : χt 2 = 0 := by
    dsimp [χt]
    have h1 : Real.smoothTransition (2 - 2) = 0 := by
      rw [show (2 : ℝ) - 2 = 0 by norm_num]
      exact Real.smoothTransition.zero
    rw [h1, zero_mul]
  have hsec : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun s : ℝ => (⟨s, (f s : TangentSpace 𝓘(ℝ, ℝ) s)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    intro y
    rw [Bundle.contMDiffAt_totalSpace]
    constructor
    · exact contMDiffAt_id
    · have hρx : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s : ℝ => ρ (x, s)) :=
        hρ_sm.comp (contMDiff_const.prodMk contMDiff_id)
      have hχt : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) χt := by
        dsimp [χt]
        exact ((Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)).mul
          (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const))).contMDiff
      have hf : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) f y := by
        dsimp [f]
        exact (hρx.mul hχt).contMDiffAt
      have heq : ∀ s : ℝ, (trivializationAt ℝ (TangentSpace 𝓘(ℝ, ℝ)) y
          (⟨s, (f s : TangentSpace 𝓘(ℝ, ℝ) s)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)).2 = f s := by
        intro s
        simp
      exact hf.congr_of_eventuallyEq (Filter.Eventually.of_forall heq)
  have hσ' : IsMIntegralCurve (I := 𝓘(ℝ, ℝ)) (M := ℝ) (E := ℝ) (H := ℝ) σ
      (fun s : ℝ => (f s : TangentSpace 𝓘(ℝ, ℝ) s)) := by
    simpa [f, χt, mul_assoc] using hσ
  intro t
  have hne_m1 : ∀ c : ℝ, σ c ≠ -1 := by
    intro c h
    have hc : IsMIntegralCurve (I := 𝓘(ℝ, ℝ)) (M := ℝ) (E := ℝ) (H := ℝ)
        (fun _ : ℝ => (-1 : ℝ)) (fun s : ℝ => (f s : TangentSpace 𝓘(ℝ, ℝ) s)) :=
      isMIntegralCurve_iff_isMIntegralCurveOn.mpr
        (isMIntegralCurveOn_const_of_eq_zero (I := 𝓘(ℝ, ℝ)) (M := ℝ) (E := ℝ) (H := ℝ)
          (v := fun s : ℝ => (f s : TangentSpace 𝓘(ℝ, ℝ) s)) (-1 : ℝ) (by
            dsimp [f]
            rw [hχt_m1]
            simp
            rfl))
    have heq : σ = fun _ : ℝ => (-1 : ℝ) := by
      exact isMIntegralCurve_eq_of_contMDiff (t₀ := c)
        (I := 𝓘(ℝ, ℝ)) (H := ℝ) (M := ℝ) (E := ℝ)
        (v := fun s : ℝ => (f s : TangentSpace 𝓘(ℝ, ℝ) s))
        (γ := σ) (γ' := fun _ : ℝ => (-1 : ℝ))
        (hv := hsec.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞))
        (fun t : ℝ => BoundarylessManifold.isInteriorPoint (I := 𝓘(ℝ, ℝ)) (M := ℝ) (x := σ t))
        hσ' hc (by
          simpa using h)
    have hc0 : σ 0 = -1 := by rw [heq]
    linarith [hσ0, hs₀.1, hc0]
  have hne_2 : ∀ c : ℝ, σ c ≠ 2 := by
    intro c h
    have hc : IsMIntegralCurve (I := 𝓘(ℝ, ℝ)) (M := ℝ) (E := ℝ) (H := ℝ)
        (fun _ : ℝ => (2 : ℝ)) (fun s : ℝ => (f s : TangentSpace 𝓘(ℝ, ℝ) s)) :=
      isMIntegralCurve_iff_isMIntegralCurveOn.mpr
        (isMIntegralCurveOn_const_of_eq_zero (I := 𝓘(ℝ, ℝ)) (M := ℝ) (E := ℝ) (H := ℝ)
          (v := fun s : ℝ => (f s : TangentSpace 𝓘(ℝ, ℝ) s)) (2 : ℝ) (by
            dsimp [f]
            rw [hχt_2]
            simp
            rfl))
    have heq : σ = fun _ : ℝ => (2 : ℝ) := by
      exact isMIntegralCurve_eq_of_contMDiff (t₀ := c)
        (I := 𝓘(ℝ, ℝ)) (H := ℝ) (M := ℝ) (E := ℝ)
        (v := fun s : ℝ => (f s : TangentSpace 𝓘(ℝ, ℝ) s))
        (γ := σ) (γ' := fun _ : ℝ => (2 : ℝ))
        (hv := hsec.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞))
        (fun t : ℝ => BoundarylessManifold.isInteriorPoint (I := 𝓘(ℝ, ℝ)) (M := ℝ) (x := σ t))
        hσ' hc (by
          simpa using h)
    have hc0 : σ 0 = 2 := by rw [heq]
    linarith [hσ0, hs₀.2, hc0]
  have hle1 : -1 < σ t := by
    by_contra hnot
    have hle : σ t ≤ -1 := le_of_not_gt hnot
    have hmem : -1 ∈ Set.uIcc (σ 0) (σ t) := by
      rw [hσ0]
      change min s₀ (σ t) ≤ -1 ∧ -1 ≤ max s₀ (σ t)
      constructor
      · have hmin : min s₀ (σ t) = σ t := by
          apply min_eq_right
          linarith [hs₀.1, hle]
        rw [hmin]
        exact hle
      · have hmax : max s₀ (σ t) = s₀ := by
          apply max_eq_left
          linarith [hs₀.1, hle]
        rw [hmax]
        linarith [hs₀.1]
    have himg := intermediate_value_uIcc (f := σ) (a := 0) (b := t)
      (hf := (continuousOn_univ.mpr hσ.continuous).mono (by intro z hz; trivial))
    rcases himg hmem with ⟨c, hc, hcval⟩
    exact hne_m1 c hcval
  have hle2 : σ t < 2 := by
    by_contra hnot
    have hge : 2 ≤ σ t := le_of_not_gt hnot
    have hmem : 2 ∈ Set.uIcc (σ 0) (σ t) := by
      rw [hσ0]
      change min s₀ (σ t) ≤ 2 ∧ 2 ≤ max s₀ (σ t)
      constructor
      · have hmin : min s₀ (σ t) = s₀ := by
          apply min_eq_left
          linarith [hs₀.2, hge]
        rw [hmin]
        linarith [hs₀.2]
      · have hmax : max s₀ (σ t) = σ t := by
          apply max_eq_right
          linarith [hs₀.2, hge]
        rw [hmax]
        exact hge
    have himg := intermediate_value_uIcc (f := σ) (a := 0) (b := t)
      (hf := (continuousOn_univ.mpr hσ.continuous).mono (by intro z hz; trivial))
    rcases himg hmem with ⟨c, hc, hcval⟩
    exact hne_2 c hcval
  exact ⟨hle1, hle2⟩

private lemma pairFlow_aux_curve_integral
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H}
    {χs : M × ℝ → ℝ} {ρ : M × ℝ → ℝ} {χt : ℝ → ℝ}
    {w : (x : M) → (s : ℝ) → TangentSpace I x}
    (Vsusp : (q : M × ℝ) → TangentSpace (I.prod 𝓘(ℝ, ℝ)) q)
    (hVsusp : Vsusp = fun q : M × ℝ => (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) q from
      (χs q • w q.1 q.2, ρ q * χt q.2)))
    {y : M} {τ : ℝ → ℝ}
    (hτIs : IsMIntegralCurve (I := 𝓘(ℝ, ℝ)) (M := ℝ) (E := ℝ) (H := ℝ) τ
      (fun s : ℝ => (ρ (y, s) * χt s : TangentSpace 𝓘(ℝ, ℝ) s)))
    (hχs : ∀ s : ℝ, χs (y, s) = 0) :
    IsMIntegralCurve (fun u : ℝ => (y, τ u)) Vsusp := by
  intro u
  have hτ' : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) τ u
      ((1 : ℝ →L[ℝ] ℝ).smulRight (ρ (y, τ u) * χt (τ u))) := hτIs u
  have hpair : HasMFDerivAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (fun u : ℝ => (y, τ u)) u
      ((0 : TangentSpace 𝓘(ℝ, ℝ) u →L[ℝ] TangentSpace I y).prod
        ((1 : ℝ →L[ℝ] ℝ).smulRight (ρ (y, τ u) * χt (τ u)))) := by
    simpa using (hasMFDerivAt_const (c := y) (x := u)).prodMk hτ'
  have hV : Vsusp (y, τ u) = (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (y, τ u) from
      (χs (y, τ u) • w y (τ u), ρ (y, τ u) * χt (τ u))) := by
    rw [hVsusp]
  have hχs0 : χs (y, τ u) = 0 := hχs (τ u)
  have hderiv_eq : (0 : TangentSpace 𝓘(ℝ, ℝ) u →L[ℝ] TangentSpace I y).prod
      ((1 : ℝ →L[ℝ] ℝ).smulRight (ρ (y, τ u) * χt (τ u))) =
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Vsusp (y, τ u))) := by
    apply ContinuousLinearMap.ext_ring
    change ((0 : TangentSpace 𝓘(ℝ, ℝ) u →L[ℝ] TangentSpace I y) (1 : ℝ),
        ((1 : ℝ →L[ℝ] ℝ).smulRight (ρ (y, τ u) * χt (τ u))) (1 : ℝ)) =
      ((1 : ℝ →L[ℝ] ℝ) (1 : ℝ) • Vsusp (y, τ u))
    rw [hV]
    rw [hχs0]
    simp [ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    rfl
  exact hpair.congr_mfderiv hderiv_eq

private lemma orbit_spatial_mem_projection
    {I : ModelWithCorners ℝ (MorseModel (m + 1)) H} [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    {χs : M × ℝ → ℝ} {ρ : M × ℝ → ℝ} {χt : ℝ → ℝ}
    {w : (x : M) → (s : ℝ) → TangentSpace I x}
    (hχs_sm : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) χs)
    (hχs_supp : IsCompact (tsupport χs))
    (hρ_sm : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hχt_sm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) χt)
    (hχt_supp : IsCompact (tsupport χt))
    (Vsusp : (q : M × ℝ) → TangentSpace (I.prod 𝓘(ℝ, ℝ)) q)
    (hVsusp : Vsusp = fun q : M × ℝ => (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) q from
      (χs q • w q.1 q.2, ρ q * χt q.2)))
    (hVsuspsec : ContMDiff (I.prod 𝓘(ℝ, ℝ)) ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, (MorseModel (m + 1)) × ℝ))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q, Vsusp q⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))))
    (hcomplete : ∀ p : M × ℝ, ∃ γ : ℝ → M × ℝ, γ 0 = p ∧ IsMIntegralCurve γ Vsusp)
    (x₀ : M) (s₀ : ℝ) (hx₀ : x₀ ∈ Prod.fst '' tsupport χs) :
    (∀ t : ℝ, t ∈ Set.Icc 0 1 → (curveAt Vsusp hcomplete (x₀, s₀) t).1 ∈ Prod.fst '' tsupport χs) ∧
    (∀ t : ℝ, t ∈ Set.Icc (-1) 0 → (curveAt Vsusp hcomplete (x₀, s₀) t).1 ∈ Prod.fst '' tsupport χs) := by
  classical
  let A : Set M := Prod.fst '' tsupport χs
  have hAcl : IsClosed A := (hχs_supp.image continuous_fst).isClosed
  have hχs_out : ∀ q : M × ℝ, q.1 ∉ A → χs q = 0 := by
    intro q hq
    by_contra h
    have hts : q ∈ tsupport χs := subset_closure (by simpa [Function.support] using h)
    exact hq ⟨q, hts, rfl⟩
  have hχs_Acl : ∀ y : M, y ∈ A → y ∈ closure (Set.compl A) → ∀ s : ℝ, χs (y, s) = 0 := by
    intro y hyA hycl s
    by_contra hne
    have hcont : ContinuousAt (fun z : M => χs (z, s)) y := by
      exact (hχs_sm.continuous.comp (continuous_id.prodMk continuous_const)).continuousAt
    have hU : {z : M | χs (z, s) ≠ 0} ∈ nhds y := by
      exact hcont.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hne)
    rcases (mem_closure_iff_nhds.mp hycl) {z : M | χs (z, s) ≠ 0} hU with ⟨z, hzU, hzA⟩
    exact hzU (hχs_out (z, s) hzA)
  have hfrontier_orbit : ∀ (y : M) (t₀ : ℝ), y ∈ A → y ∈ closure (Set.compl A) →
      ∀ t : ℝ, (curveAt Vsusp hcomplete (y, t₀) t).1 = y := by
    intro y t₀ hyA hycl t
    rcases exists_scalar_flow_smooth_cutoff (I := I) (ρ := ρ) (χt := χt)
      hρ_sm hχt_sm hχt_supp y t₀ with ⟨τ, hτ0, hτIs⟩
    let c : ℝ → M × ℝ := fun u => (y, τ u)
    have hcIs : IsMIntegralCurve c Vsusp := by
      exact pairFlow_aux_curve_integral (I := I) (Vsusp := Vsusp) (hVsusp := hVsusp)
        (τ := τ) (hτIs := hτIs) (hχs := fun s => hχs_Acl y hyA hycl s)
    have heq : curveAt Vsusp hcomplete (y, t₀) = c := by
      exact isMIntegralCurve_eq_of_contMDiff (t₀ := 0)
        (I := I.prod 𝓘(ℝ, ℝ)) (v := Vsusp) (γ := curveAt Vsusp hcomplete (y, t₀)) (γ' := c)
        (hv := hVsuspsec.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞))
        (fun t => BoundarylessManifold.isInteriorPoint (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ)
          (x := curveAt Vsusp hcomplete (y, t₀) t))
        (curveAt_integralCurve Vsusp hcomplete (y, t₀)) hcIs
        (by
          dsimp [c]
          rw [hτ0, curveAt_zero Vsusp hcomplete (y, t₀)])
    change (curveAt Vsusp hcomplete (y, t₀) t).1 = y
    simpa [c] using congrArg Prod.fst (congrFun heq t)
  have hA_inv_fwd : ∀ t : ℝ, t ∈ Set.Icc 0 1 →
      (curveAt Vsusp hcomplete (x₀, s₀) t).1 ∈ A := by
    intro t ht
    by_contra hnot
    have ht0 : 0 < t := by
      rcases lt_or_eq_of_le ht.1 with hlt | heq
      · exact hlt
      · exfalso
        exact hnot (by
          rw [heq.symm]
          rw [curveAt_zero Vsusp hcomplete (x₀, s₀)]
          simpa [A] using hx₀)
    have hcont : Continuous (fun u : ℝ => (curveAt Vsusp hcomplete (x₀, s₀) u).1) := by
      have hγc : Continuous (curveAt Vsusp hcomplete (x₀, s₀)) :=
        continuous_iff_continuousAt.mpr (fun u =>
          (curveAt_integralCurve Vsusp hcomplete (x₀, s₀) u).continuousAt)
      exact continuous_fst.comp hγc
    have hcompl_open : IsOpen (Set.compl A) := hAcl.isOpen_compl
    have hpre : {u : ℝ | (curveAt Vsusp hcomplete (x₀, s₀) u).1 ∉ A} ∈ nhds t :=
      hcont.continuousAt.preimage_mem_nhds (hcompl_open.mem_nhds hnot)
    rcases Metric.mem_nhds_iff.mp hpre with ⟨δ, hδ, hball⟩
    let u₁ : ℝ := t - min (δ / 2) (t / 2)
    let m : ℝ := min (δ / 2) (t / 2)
    have hmin_lt : m < t := by
      dsimp [m]
      exact lt_of_le_of_lt (min_le_right (δ / 2) (t / 2)) (by linarith)
    have hmin_pos : 0 < m := by
      dsimp [m]
      exact lt_min (half_pos hδ) (half_pos ht0)
    have hu₁ : 0 < u₁ ∧ u₁ < t := by
      constructor
      · dsimp [u₁]
        linarith [hmin_lt]
      · dsimp [u₁]
        linarith [hmin_pos]
    have hu₁S : (curveAt Vsusp hcomplete (x₀, s₀) u₁).1 ∉ A := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      rw [abs_of_neg (sub_neg.mpr hu₁.2)]
      dsimp [u₁]
      have hminle : min (δ / 2) (t / 2) ≤ δ / 2 := min_le_left (δ / 2) (t / 2)
      nlinarith [hδ]
    let S : Set ℝ := {u : ℝ | u ∈ Set.Ioo 0 t ∧ (curveAt Vsusp hcomplete (x₀, s₀) u).1 ∉ A}
    have hSne : S.Nonempty := ⟨u₁, ⟨hu₁, hu₁S⟩⟩
    have hSbdd : BddBelow S := ⟨0, by intro u hu; exact le_of_lt hu.1.1⟩
    let t₀ : ℝ := sInf S
    have ht₀ge : 0 ≤ t₀ := le_csInf hSne (by intro u hu; exact le_of_lt hu.1.1)
    have ht₀lt : t₀ < t := by
      have hle : t₀ ≤ u₁ := csInf_le hSbdd ⟨hu₁, hu₁S⟩
      linarith
    have hx_in_A_below : ∀ u : ℝ, u ∈ Set.Ico 0 t₀ →
        (curveAt Vsusp hcomplete (x₀, s₀) u).1 ∈ A := by
      intro u hu
      by_cases hu0 : u = 0
      · exact (by
          rw [hu0]
          rw [curveAt_zero Vsusp hcomplete (x₀, s₀)]
          simpa [A] using hx₀)
      · have hpos : 0 < u := lt_of_le_of_ne hu.1 (by intro h; exact hu0 h.symm)
        by_contra hnotA
        have huS : u ∈ S := ⟨⟨hpos, lt_of_lt_of_le hu.2 (le_of_lt ht₀lt)⟩, hnotA⟩
        have hle₀ : t₀ ≤ u := csInf_le hSbdd huS
        exact (not_lt_of_ge hle₀) hu.2
    have hx_t₀ : (curveAt Vsusp hcomplete (x₀, s₀) t₀).1 ∈ A := by
      by_cases ht₀eq : t₀ = 0
      · exact (by
          rw [ht₀eq]
          rw [curveAt_zero Vsusp hcomplete (x₀, s₀)]
          simpa [A] using hx₀)
      · have hcl : t₀ ∈ closure (Set.Ico 0 t₀) := by
          rw [closure_Ico (by intro h; exact ht₀eq h.symm)]
          exact ⟨ht₀ge, le_rfl⟩
        have hlim : Tendsto (fun u : ℝ => (curveAt Vsusp hcomplete (x₀, s₀) u).1)
            (nhdsWithin t₀ (Set.Ico 0 t₀)) (nhds ((curveAt Vsusp hcomplete (x₀, s₀) t₀).1)) :=
          hcont.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ico 0 t₀) (a := t₀))
        have hxIco : ∀ᶠ u in nhdsWithin t₀ (Set.Ico 0 t₀),
            (curveAt Vsusp hcomplete (x₀, s₀) u).1 ∈ A := by
          rw [Filter.eventually_iff_exists_mem]
          exact ⟨Set.Ico 0 t₀, self_mem_nhdsWithin,
            by intro u hu; exact hx_in_A_below u hu⟩
        haveI : (nhdsWithin t₀ (Set.Ico 0 t₀)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
        exact hAcl.mem_of_tendsto hlim hxIco
    have hx_t₀_cl : (curveAt Vsusp hcomplete (x₀, s₀) t₀).1 ∈ closure (Set.compl A) := by
      have hclS : t₀ ∈ closure S := csInf_mem_closure hSne hSbdd
      have hlim : Tendsto (fun u : ℝ => (curveAt Vsusp hcomplete (x₀, s₀) u).1)
          (nhdsWithin t₀ S) (nhds ((curveAt Vsusp hcomplete (x₀, s₀) t₀).1)) :=
        hcont.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := S) (a := t₀))
      have hxS : ∀ᶠ u in nhdsWithin t₀ S, (curveAt Vsusp hcomplete (x₀, s₀) u).1 ∈ Set.compl A := by
        rw [Filter.eventually_iff_exists_mem]
        exact ⟨S, self_mem_nhdsWithin, by intro u hu; exact hu.2⟩
      haveI : (nhdsWithin t₀ S).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hclS
      have hxScl : ∀ᶠ u in nhdsWithin t₀ S,
          (curveAt Vsusp hcomplete (x₀, s₀) u).1 ∈ closure (Set.compl A) :=
        hxS.mono (by intro u hu; exact subset_closure hu)
      exact isClosed_closure.mem_of_tendsto hlim hxScl
    have hyorbit : ∀ u : ℝ,
        (curveAt Vsusp hcomplete (curveAt Vsusp hcomplete (x₀, s₀) t₀) u).1 =
          (curveAt Vsusp hcomplete (x₀, s₀) t₀).1 :=
      hfrontier_orbit (curveAt Vsusp hcomplete (x₀, s₀) t₀).1
        (curveAt Vsusp hcomplete (x₀, s₀) t₀).2 hx_t₀ hx_t₀_cl
    have hgrp : curveAt Vsusp hcomplete (curveAt Vsusp hcomplete (x₀, s₀) t₀) (t - t₀) =
        curveAt Vsusp hcomplete (x₀, s₀) t := by
      have hadd := curveAt_add Vsusp (hVsuspsec.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞))
        hcomplete (x₀, s₀) t₀ (t - t₀)
      rw [add_sub_cancel] at hadd
      exact hadd.symm
    have hx_t : (curveAt Vsusp hcomplete (x₀, s₀) t).1 = (curveAt Vsusp hcomplete (x₀, s₀) t₀).1 := by
      calc
        (curveAt Vsusp hcomplete (x₀, s₀) t).1 =
            (curveAt Vsusp hcomplete (curveAt Vsusp hcomplete (x₀, s₀) t₀) (t - t₀)).1 := by
              rw [hgrp]
        _ = (curveAt Vsusp hcomplete (x₀, s₀) t₀).1 := hyorbit (t - t₀)
    rw [hx_t] at hnot
    exact hnot hx_t₀
  have hA_inv_back : ∀ t : ℝ, t ∈ Set.Icc (-1) 0 →
      (curveAt Vsusp hcomplete (x₀, s₀) t).1 ∈ A := by
    intro t ht
    by_contra hnot
    have ht0 : t < 0 := by
      rcases lt_or_eq_of_le ht.2 with hlt | heq
      · exact hlt
      · exfalso
        exact hnot (by
          rw [heq]
          rw [curveAt_zero Vsusp hcomplete (x₀, s₀)]
          simpa [A] using hx₀)
    have hcont : Continuous (fun u : ℝ => (curveAt Vsusp hcomplete (x₀, s₀) u).1) := by
      have hγc : Continuous (curveAt Vsusp hcomplete (x₀, s₀)) :=
        continuous_iff_continuousAt.mpr (fun u =>
          (curveAt_integralCurve Vsusp hcomplete (x₀, s₀) u).continuousAt)
      exact continuous_fst.comp hγc
    have hcompl_open : IsOpen (Set.compl A) := hAcl.isOpen_compl
    have hpre : {u : ℝ | (curveAt Vsusp hcomplete (x₀, s₀) u).1 ∉ A} ∈ nhds t :=
      hcont.continuousAt.preimage_mem_nhds (hcompl_open.mem_nhds hnot)
    rcases Metric.mem_nhds_iff.mp hpre with ⟨δ, hδ, hball⟩
    let u₁ : ℝ := t + min (δ / 2) ((-t) / 2)
    let m : ℝ := min (δ / 2) ((-t) / 2)
    have hmin_lt : m < -t := by
      dsimp [m]
      exact lt_of_le_of_lt (min_le_right (δ / 2) ((-t) / 2)) (by linarith)
    have hmin_pos : 0 < m := by
      dsimp [m]
      exact lt_min (half_pos hδ) (half_pos (neg_pos.mpr ht0))
    have hu₁ : t < u₁ ∧ u₁ < 0 := by
      constructor
      · dsimp [u₁]
        linarith [hmin_pos]
      · dsimp [u₁]
        linarith [hmin_lt]
    have hu₁S : (curveAt Vsusp hcomplete (x₀, s₀) u₁).1 ∉ A := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      rw [abs_of_pos (sub_pos.mpr hu₁.1)]
      dsimp [u₁]
      have hminle : min (δ / 2) ((-t) / 2) ≤ δ / 2 := min_le_left (δ / 2) ((-t) / 2)
      nlinarith [hδ]
    let S : Set ℝ := {u : ℝ | u ∈ Set.Ioo t 0 ∧ (curveAt Vsusp hcomplete (x₀, s₀) u).1 ∉ A}
    have hSne : S.Nonempty := ⟨u₁, ⟨hu₁, hu₁S⟩⟩
    have hSbdd : BddAbove S := ⟨0, by intro u hu; exact le_of_lt hu.1.2⟩
    let t₀ : ℝ := sSup S
    have ht₀le : t₀ ≤ 0 := csSup_le hSne (by intro u hu; exact le_of_lt hu.1.2)
    have ht₀gt : t < t₀ := by
      have hge : u₁ ≤ t₀ := le_csSup hSbdd ⟨hu₁, hu₁S⟩
      linarith
    have hx_in_A_above : ∀ u : ℝ, u ∈ Set.Ioc t₀ 0 →
        (curveAt Vsusp hcomplete (x₀, s₀) u).1 ∈ A := by
      intro u hu
      by_cases hu0 : u = 0
      · exact (by
          rw [hu0]
          rw [curveAt_zero Vsusp hcomplete (x₀, s₀)]
          simpa [A] using hx₀)
      · have hneg : u < 0 := lt_of_le_of_ne hu.2 (by intro h; exact hu0 h)
        by_contra hnotA
        have huS : u ∈ S := ⟨⟨lt_of_lt_of_le ht₀gt (le_of_lt hu.1), hneg⟩, hnotA⟩
        have hle₀ : u ≤ t₀ := le_csSup hSbdd huS
        exact (not_lt_of_ge hle₀) hu.1
    have hx_t₀ : (curveAt Vsusp hcomplete (x₀, s₀) t₀).1 ∈ A := by
      by_cases ht₀eq : t₀ = 0
      · exact (by
          rw [ht₀eq]
          rw [curveAt_zero Vsusp hcomplete (x₀, s₀)]
          simpa [A] using hx₀)
      · have ht₀ne : t₀ ≠ 0 := ht₀eq
        have hcl : t₀ ∈ closure (Set.Ioc t₀ 0) := by
          rw [closure_Ioc ht₀ne]
          exact ⟨le_rfl, ht₀le⟩
        have hlim : Tendsto (fun u : ℝ => (curveAt Vsusp hcomplete (x₀, s₀) u).1)
            (nhdsWithin t₀ (Set.Ioc t₀ 0)) (nhds ((curveAt Vsusp hcomplete (x₀, s₀) t₀).1)) :=
          hcont.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioc t₀ 0) (a := t₀))
        have hxIoc : ∀ᶠ u in nhdsWithin t₀ (Set.Ioc t₀ 0),
            (curveAt Vsusp hcomplete (x₀, s₀) u).1 ∈ A := by
          rw [Filter.eventually_iff_exists_mem]
          exact ⟨Set.Ioc t₀ 0, self_mem_nhdsWithin,
            by intro u hu; exact hx_in_A_above u hu⟩
        haveI : (nhdsWithin t₀ (Set.Ioc t₀ 0)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
        exact hAcl.mem_of_tendsto hlim hxIoc
    have hx_t₀_cl : (curveAt Vsusp hcomplete (x₀, s₀) t₀).1 ∈ closure (Set.compl A) := by
      have hclS : t₀ ∈ closure S := csSup_mem_closure hSne hSbdd
      have hlim : Tendsto (fun u : ℝ => (curveAt Vsusp hcomplete (x₀, s₀) u).1)
          (nhdsWithin t₀ S) (nhds ((curveAt Vsusp hcomplete (x₀, s₀) t₀).1)) :=
        hcont.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := S) (a := t₀))
      have hxS : ∀ᶠ u in nhdsWithin t₀ S, (curveAt Vsusp hcomplete (x₀, s₀) u).1 ∈ Set.compl A := by
        rw [Filter.eventually_iff_exists_mem]
        exact ⟨S, self_mem_nhdsWithin, by intro u hu; exact hu.2⟩
      haveI : (nhdsWithin t₀ S).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hclS
      have hxScl : ∀ᶠ u in nhdsWithin t₀ S,
          (curveAt Vsusp hcomplete (x₀, s₀) u).1 ∈ closure (Set.compl A) :=
        hxS.mono (by intro u hu; exact subset_closure hu)
      exact isClosed_closure.mem_of_tendsto hlim hxScl
    have hyorbit : ∀ u : ℝ,
        (curveAt Vsusp hcomplete (curveAt Vsusp hcomplete (x₀, s₀) t₀) u).1 =
          (curveAt Vsusp hcomplete (x₀, s₀) t₀).1 :=
      hfrontier_orbit (curveAt Vsusp hcomplete (x₀, s₀) t₀).1
        (curveAt Vsusp hcomplete (x₀, s₀) t₀).2 hx_t₀ hx_t₀_cl
    have hgrp : curveAt Vsusp hcomplete (curveAt Vsusp hcomplete (x₀, s₀) t₀) (t - t₀) =
        curveAt Vsusp hcomplete (x₀, s₀) t := by
      have hadd := curveAt_add Vsusp (hVsuspsec.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞))
        hcomplete (x₀, s₀) t₀ (t - t₀)
      rw [add_sub_cancel] at hadd
      exact hadd.symm
    have hx_t : (curveAt Vsusp hcomplete (x₀, s₀) t).1 = (curveAt Vsusp hcomplete (x₀, s₀) t₀).1 := by
      calc
        (curveAt Vsusp hcomplete (x₀, s₀) t).1 =
            (curveAt Vsusp hcomplete (curveAt Vsusp hcomplete (x₀, s₀) t₀) (t - t₀)).1 := by
              rw [hgrp]
        _ = (curveAt Vsusp hcomplete (x₀, s₀) t₀).1 := hyorbit (t - t₀)
    rw [hx_t] at hnot
    exact hnot hx_t₀
  exact ⟨hA_inv_fwd, hA_inv_back⟩

theorem exists_relDiffeomorph_sublevel_of_regularFamily
    (I : ModelWithCorners ℝ (MorseModel (m + 1)) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
    [FiniteDimensional ℝ (MorseModel (m + 1))] [CompleteSpace (MorseModel (m + 1))]
    (F : M → ℝ → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2))
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hstrip : IsCompact {q : M × ℝ | |F q.1 q.2| ≤ 2 * ε₀ ∧ q.2 ∈ Set.Icc 0 1})
    (hreg : ∀ q : M × ℝ, |F q.1 q.2| ≤ 2 * ε₀ → q.2 ∈ Set.Icc 0 1 →
      ¬ IsCriticalPointAt I (fun x : M => F x q.2) q.1)
    (D : Set M) (hDcl : IsClosed D)
    (hDsep : ∀ x : M, x ∈ D → ∀ s : ℝ, s ∈ Set.Icc 0 1 → 2 * ε₀ < |F x s|)
    (hDsign : ∀ x : M, x ∈ D → (F x 0 ≤ 0 ↔ F x 1 ≤ 0)) :
    ∃ (Φ Ψ : M → M),
      ContMDiff I I (↑(⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧
      ContMDiff I I (↑(⊤ : ℕ∞) : WithTop ℕ∞) Ψ ∧
      (∀ x : M, x ∈ D → Φ x = x ∧ Ψ x = x) ∧
      (∀ x : M, F x 0 ≤ 0 → F (Φ x) 1 ≤ 0) ∧
      (∀ y : M, F y 1 ≤ 0 → F (Ψ y) 0 ≤ 0) ∧
      (∀ x : M, F x 0 = 0 → F (Φ x) 1 = 0) ∧
      (∀ y : M, F y 1 = 0 → F (Ψ y) 0 = 0) ∧
      (∀ x : M, F x 0 < 0 → F (Φ x) 1 < 0) ∧
      (∀ y : M, F y 1 < 0 → F (Ψ y) 0 < 0) ∧
      (∀ x : M, F x 0 ≤ 0 → Ψ (Φ x) = x) ∧
      (∀ y : M, F y 1 ≤ 0 → Φ (Ψ y) = y) := by
  classical
  let K : Set (M × ℝ) := {q : M × ℝ | |F q.1 q.2| ≤ 2 * ε₀ ∧ q.2 ∈ Set.Icc 0 1}
  have hK : IsCompact K := hstrip
  have hKcl : IsClosed K := hK.isClosed
  have hKreg : ∀ p ∈ K, ¬ IsCriticalPointAt I (fun x : M => F x p.2) p.1 := by
    intro p hp
    exact hreg p hp.1 hp.2
  rcases exists_unitSpeedFamilyVectorField_on_compact I F hF K hK hKreg with
    ⟨V, hVsec, hVsupp, hVdf, hVdfbdd⟩
  have hdt : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (fderiv ℝ (fun t : ℝ => F q.1 t) q.2) 1) :=
    familyTimeDeriv_contMDiff (I := I) F hF
  let w : (x : M) → (s : ℝ) → TangentSpace I x := fun x s =>
    ((fderiv ℝ (fun t : ℝ => F x t) s) 1) • V x s
  have hwsec : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, MorseModel (m + 1))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q.1, w q.1 q.2⟩ : TangentBundle I M)) := by
    exact familyTangentSection_smul_of_tsupport (I := I) (W := V)
      (ψ := fun q => (fderiv ℝ (fun t : ℝ => F q.1 t) q.2) 1) (u := Set.univ)
      (by intro q hq; exact hdt q) isOpen_univ (by simp) (by intro q hq; exact hVsec q)
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let D01 : Set (M × ℝ) := D ×ˢ Set.Icc (-1) 2
  have hD01closed : IsClosed D01 := hDcl.prod isClosed_Icc
  have hKsubD01 : K ⊆ Set.compl D01 := by
    intro q hq
    by_cases hnot : q ∈ D01
    · exfalso
      have hxD : q.1 ∈ D := hnot.1
      have hs : q.2 ∈ Set.Icc (-1) 2 := hnot.2
      have hs01 : q.2 ∈ Set.Icc 0 1 := hq.2
      have hsep := hDsep q.1 hxD q.2 hs01
      nlinarith [hq.1, hsep]
    · exact hnot
  have hD01open : IsOpen (Set.compl D01) := hD01closed.isOpen_compl
  rcases exists_open_between_and_isCompact_closure hK hD01open hKsubD01 with
    ⟨U₀, hU₀open, hKU₀, hU₀cl, hU₀compact⟩
  rcases SmoothPartitionOfUnity.exists_isSubordinate (I := I.prod 𝓘(ℝ, ℝ)) (s := K)
    (U := fun i : Fin 2 => if i = 0 then U₀ else (Set.compl K)) (hs := hKcl)
    (ho := by
      intro i
      by_cases hi : i = 0
      · have hopen : IsOpen U₀ := hU₀open
        simpa [hi] using hopen
      · have hopen : IsOpen (Set.compl K) := hKcl.isOpen_compl
        simpa [hi] using hopen)
    (hU := by
      intro q hq
      refine Set.mem_iUnion.mpr ?_
      exact ⟨0, by simpa using hKU₀ hq⟩) with ⟨ρsp, hρspsub⟩
  let χs : M × ℝ → ℝ := ρsp 0
  have hχs_sm : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) χs := by
    exact (ρsp 0).property
  have hχsK : ∀ q : M × ℝ, q ∈ K → χs q = 1 := by
    intro q hq
    dsimp [χs]
    have hsum : (∑ᶠ i : Fin 2, ρsp i q) = 1 := ρsp.sum_eq_one hq
    have hρ1 : ρsp 1 q = 0 := by
      have hts : q ∉ tsupport (ρsp 1) := by
        intro ht
        have hsub := hρspsub 1 ht
        have hsub' : q ∈ Set.compl K := by simpa using hsub
        have hqnot : q ∉ Set.compl K := by
          intro hc
          exact (by simpa [Set.mem_compl_iff] using hc : q ∉ K) hq
        exact False.elim (hqnot hsub')
      exact image_eq_zero_of_notMem_tsupport hts
    have hfin : (∑ᶠ i : Fin 2, ρsp i q) = ρsp 0 q + ρsp 1 q := by
      rw [finsum_eq_sum_of_fintype]
      simp
    rw [hfin, hρ1] at hsum
    linarith
  have hχs_supp : IsCompact (tsupport χs) := by
    have hts : tsupport χs ⊆ closure U₀ := by
      exact (hρspsub 0).trans subset_closure
    exact hU₀compact.of_isClosed_subset (isClosed_tsupport χs) hts
  have hχsD : ∀ x : M, x ∈ D → ∀ s : ℝ, s ∈ Set.Ioo (-1) 2 → χs (x, s) = 0 := by
    intro x hxD s hs
    have hnot : (x, s) ∉ tsupport χs := by
      intro hts
      have hcl : (x, s) ∈ closure U₀ := (hρspsub 0).trans subset_closure hts
      have hc : (x, s) ∈ Set.compl D01 := hU₀cl hcl
      exact hc ⟨hxD, by constructor <;> linarith [hs.1, hs.2]⟩
    exact image_eq_zero_of_notMem_tsupport hnot
  let χt : ℝ → ℝ := fun s => Real.smoothTransition (2 - s) * Real.smoothTransition (s + 1)
  have hχt_sm : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) χt := by
    dsimp [χt]
    exact ((Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)).mul
      (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const))).contMDiff
  have hχt_one : ∀ s : ℝ, s ∈ Set.Icc 0 1 → χt s = 1 := by
    intro s hs
    dsimp [χt]
    have h1 : 1 ≤ 2 - s := by nlinarith [hs.2]
    have h2 : 1 ≤ s + 1 := by nlinarith [hs.1]
    rw [Real.smoothTransition.one_of_one_le h1]
    rw [Real.smoothTransition.one_of_one_le h2]
    norm_num
  have hχt_ge0 : ∀ s : ℝ, 0 ≤ χt s := by
    intro s
    dsimp [χt]
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hχt_le1 : ∀ s : ℝ, χt s ≤ 1 := by
    intro s
    dsimp [χt]
    exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.le_one _)
  have hχt_supp : IsCompact (tsupport χt) := by
    have hsupp0 : Function.support χt ⊆ Set.Icc (-1) 2 := by
      intro s hs
      dsimp [Function.support] at hs
      have hτ1ne : Real.smoothTransition (2 - s) ≠ 0 := by
        intro h
        exact hs (by dsimp [χt]; rw [h, zero_mul])
      have hτ2ne : Real.smoothTransition (s + 1) ≠ 0 := by
        intro h
        exact hs (by dsimp [χt]; rw [h, mul_zero])
      have harg1 : 0 < 2 - s := by
        by_contra h
        have hle : 2 - s ≤ 0 := le_of_not_gt h
        exact hτ1ne (Real.smoothTransition.zero_of_nonpos hle)
      have harg2 : 0 < s + 1 := by
        by_contra h
        have hle : s + 1 ≤ 0 := le_of_not_gt h
        exact hτ2ne (Real.smoothTransition.zero_of_nonpos hle)
      constructor <;> linarith
    have hts : tsupport χt ⊆ Set.Icc (-1) 2 := by
      intro s hs
      have hcl : s ∈ closure (Set.Icc (-1) 2) :=
        (closure_mono hsupp0) (by simpa [tsupport] using hs)
      simpa [isClosed_Icc.closure_eq] using hcl
    exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport χt) hts
  let A : Set M := Prod.fst '' tsupport χs
  have hAcompact : IsCompact A := hχs_supp.image continuous_fst
  have hAcl : IsClosed A := hAcompact.isClosed
  have hχs_out : ∀ q : M × ℝ, q.1 ∉ A → χs q = 0 := by
    intro q hq
    by_contra h
    have hts : q ∈ tsupport χs := subset_closure (by simpa [Function.support] using h)
    exact hq ⟨q, hts, rfl⟩
  have hK1subA : (Prod.fst '' K) ⊆ A := by
    intro y hy
    rcases hy with ⟨q, hq, rfl⟩
    have hts : q ∈ tsupport χs := subset_closure (by
      have hχ : χs q = 1 := hχsK q hq
      by_contra h0
      have h0' : χs q = 0 := not_not.mp h0
      rw [h0'] at hχ
      norm_num at hχ)
    exact ⟨q, hts, rfl⟩
  let SA : Set (M × ℝ) := A ×ˢ Set.Icc (-1) 2
  have hSAcompact : IsCompact SA := hAcompact.prod isCompact_Icc
  rcases exists_open_between_and_isCompact_closure hSAcompact isOpen_univ (subset_univ SA) with
    ⟨W, hWopen, hSW, hWcl, hWcompact⟩
  rcases SmoothPartitionOfUnity.exists_isSubordinate (I := I.prod 𝓘(ℝ, ℝ)) (s := SA)
    (U := fun i : Fin 2 => if i = 0 then W else (Set.compl SA)) (hs := hSAcompact.isClosed)
    (ho := by
      intro i
      by_cases hi : i = 0
      · have hopen : IsOpen W := hWopen
        simpa [hi] using hopen
      · have hopen : IsOpen (Set.compl SA) := hSAcompact.isClosed.isOpen_compl
        simpa [hi] using hopen)
    (hU := by
      intro q hq
      refine Set.mem_iUnion.mpr ?_
      exact ⟨0, by simpa using hSW hq⟩) with ⟨ρM, hρMsub⟩
  let ρ : M × ℝ → ℝ := ρM 0
  have hρ_sm : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) ρ := by
    exact (ρM 0).property
  have hρ01 : ∀ q : M × ℝ, ρ q ∈ Set.Icc 0 1 := by
    intro q
    dsimp [ρ]
    constructor
    · exact ρM.nonneg 0 q
    · have hsum01 : (∑ᶠ i : Fin 2, ρM i q) = ρM 0 q + ρM 1 q := by
        rw [finsum_eq_sum_of_fintype]
        simp
      have hle : ρM 0 q ≤ (∑ᶠ i : Fin 2, ρM i q) := by
        rw [hsum01]
        exact le_add_of_nonneg_right (ρM.nonneg 1 q)
      exact le_trans hle (ρM.sum_le_one q)
  have hρ_SA : ∀ q : M × ℝ, q ∈ SA → ρ q = 1 := by
    intro q hq
    dsimp [ρ]
    have hsum : (∑ᶠ i : Fin 2, ρM i q) = 1 := ρM.sum_eq_one hq
    have hρM1 : ρM 1 q = 0 := by
      have hts : q ∉ tsupport (ρM 1) := by
        intro ht
        have hsub := hρMsub 1 ht
        have hsub' : q ∈ Set.compl SA := by simpa using hsub
        have hqnot : q ∉ Set.compl SA := by
          intro hc
          exact (by simpa [Set.mem_compl_iff] using hc : q ∉ SA) hq
        exact False.elim (hqnot hsub')
      exact image_eq_zero_of_notMem_tsupport hts
    have hfin : (∑ᶠ i : Fin 2, ρM i q) = ρM 0 q + ρM 1 q := by
      rw [finsum_eq_sum_of_fintype]
      simp
    rw [hfin, hρM1] at hsum
    linarith
  have hρ_supp : IsCompact (tsupport ρ) := by
    have hts : tsupport ρ ⊆ closure W := by
      exact (hρMsub 0).trans subset_closure
    exact hWcompact.of_isClosed_subset (isClosed_tsupport ρ) hts
  let Vsusp : (q : M × ℝ) → TangentSpace (I.prod 𝓘(ℝ, ℝ)) q := fun q =>
    (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) q from (χs q • w q.1 q.2, ρ q * χt q.2))
  have hVsusp : Vsusp = fun q : M × ℝ => (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) q from
      (χs q • w q.1 q.2, ρ q * χt q.2)) := rfl
  have hVsuspsec : ContMDiff (I.prod 𝓘(ℝ, ℝ)) ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, (MorseModel (m + 1)) × ℝ))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => (⟨q, Vsusp q⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
    have hβ_sm : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : M × ℝ => ρ q * χt q.2) :=
      hρ_sm.mul (hχt_sm.comp (contMDiff_snd (I := I) (J := 𝓘(ℝ, ℝ))))
    exact suspensionSection_smul2_contMDiff (I := I) (W := w) (α := χs)
      (β := fun q : M × ℝ => ρ q * χt q.2) hwsec hχs_sm hβ_sm
  have hVsuspsupp : IsCompact (tsupport Vsusp) := by
    have hsub : Function.support Vsusp ⊆ Function.support (fun q : M × ℝ => χs q • w q.1 q.2) ∪
        Function.support (fun q : M × ℝ => ρ q * χt q.2) := by
      intro q hq
      by_cases hsp : (χs q • w q.1 q.2) = 0
      · right
        by_contra htime0
        have htime0' : ρ q * χt q.2 = 0 := not_not.mp htime0
        exact hq (by
          dsimp [Vsusp]
          change (χs q • w q.1 q.2, ρ q * χt q.2) =
            ((0 : TangentSpace I q.1), (0 : TangentSpace 𝓘(ℝ, ℝ) q.2))
          simp [hsp, htime0']
          rfl)
      · left
        exact hsp
    have hswsub : Function.support (fun q : M × ℝ => χs q • w q.1 q.2) ⊆ Function.support χs := by
      intro q hq
      by_contra hχ0
      have hχ0' : χs q = 0 := not_not.mp hχ0
      exact hq (by
        dsimp
        rw [hχ0']
        rw [zero_smul]
        rfl)
    have hsw : tsupport (fun q : M × ℝ => χs q • w q.1 q.2) ⊆ tsupport χs := by
      exact closure_mono hswsub
    have hρt_ts : tsupport (fun q : M × ℝ => ρ q * χt q.2) ⊆
        tsupport ρ ∩ ((Set.univ : Set M) ×ˢ tsupport χt) := by
      have hsub1 : Function.support (fun q : M × ℝ => ρ q * χt q.2) ⊆ Function.support ρ := by
        intro q hq
        by_contra hρ0
        have hρ0' : ρ q = 0 := not_not.mp hρ0
        exact hq (by dsimp; rw [hρ0']; norm_num)
      have hsub2 : Function.support (fun q : M × ℝ => ρ q * χt q.2) ⊆
          (Set.univ : Set M) ×ˢ Function.support χt := by
        intro q hq
        constructor
        · trivial
        · by_contra hχ0
          have hχ0' : χt q.2 = 0 := not_not.mp hχ0
          exact hq (by dsimp; rw [hχ0']; norm_num)
      have hcl1 : closure (Function.support (fun q : M × ℝ => ρ q * χt q.2)) ⊆ tsupport ρ := by
        exact closure_mono hsub1
      have hcl2 : closure (Function.support (fun q : M × ℝ => ρ q * χt q.2)) ⊆
          (Set.univ : Set M) ×ˢ tsupport χt := by
        have hmono : closure (Function.support (fun q : M × ℝ => ρ q * χt q.2)) ⊆
            closure ((Set.univ : Set M) ×ˢ Function.support χt) :=
          closure_mono hsub2
        have hclm : closure ((Set.univ : Set M) ×ˢ Function.support χt) =
            (Set.univ : Set M) ×ˢ closure (Function.support χt) := by
          rw [closure_prod_eq]
          simp
        rw [hclm] at hmono
        exact hmono
      exact subset_inter hcl1 hcl2
    have hts : tsupport Vsusp ⊆ tsupport χs ∪
        (tsupport ρ ∩ ((Set.univ : Set M) ×ˢ tsupport χt)) := by
      calc
        tsupport Vsusp = closure (Function.support Vsusp) := rfl
        _ ⊆ closure (Function.support (fun q : M × ℝ => χs q • w q.1 q.2) ∪
            Function.support (fun q : M × ℝ => ρ q * χt q.2)) := closure_mono hsub
        _ = closure (Function.support (fun q : M × ℝ => χs q • w q.1 q.2)) ∪
            closure (Function.support (fun q : M × ℝ => ρ q * χt q.2)) := by rw [closure_union]
        _ ⊆ tsupport (fun q : M × ℝ => χs q • w q.1 q.2) ∪
            (tsupport ρ ∩ ((Set.univ : Set M) ×ˢ tsupport χt)) := by
          exact union_subset_union subset_rfl hρt_ts
        _ ⊆ tsupport χs ∪ (tsupport ρ ∩ ((Set.univ : Set M) ×ˢ tsupport χt)) := by
          exact union_subset_union_left
            (tsupport ρ ∩ ((Set.univ : Set M) ×ˢ tsupport χt)) hsw
    have htsupp2 : IsCompact (tsupport ρ ∩ ((Set.univ : Set M) ×ˢ tsupport χt)) := by
      have hpre : ((Set.univ : Set M) ×ˢ tsupport χt) = Prod.snd ⁻¹' tsupport χt := by
        ext q
        simp
      have hcl : IsClosed (tsupport ρ ∩ ((Set.univ : Set M) ×ˢ tsupport χt)) := by
        rw [hpre]
        exact (isClosed_tsupport ρ).inter (IsClosed.preimage continuous_snd (isClosed_tsupport χt))
      exact hρ_supp.of_isClosed_subset hcl (by intro q hq; exact hq.1)
    exact (hχs_supp.union htsupp2).of_isClosed_subset (isClosed_tsupport Vsusp) hts
  have hcomplete : ∀ p : M × ℝ, ∃ γ : ℝ → M × ℝ, γ 0 = p ∧ IsMIntegralCurve γ Vsusp :=
    exists_globalIntegralCurve_of_compactSupport Vsusp hVsuspsec hVsuspsupp
  have hflowsm : ContMDiff (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ℝ))) (I.prod 𝓘(ℝ, ℝ)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × (M × ℝ) => curveAt Vsusp hcomplete p.2 p.1) :=
    contMDiff_globalFlow_joint_of_compactSupport Vsusp hVsuspsec hVsuspsupp
  let Φ : M → M := fun x => (curveAt Vsusp hcomplete (x, 0) 1).1
  let Ψ : M → M := fun y => (curveAt Vsusp hcomplete (y, 1) (-1)).1
  let β : M × ℝ → ℝ := fun q => ρ q * χt q.2
  have hVsuspχt : ∀ q : M × ℝ, (Vsusp q).2 = β q := by
    intro q
    simp [Vsusp, β]
  have hsnd_deriv : ∀ (p : M × ℝ) (u : ℝ), HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun t : ℝ => (curveAt Vsusp hcomplete p t).2) u
      ((1 : ℝ →L[ℝ] ℝ).smulRight (β (curveAt Vsusp hcomplete p u))) := by
    intro p u
    have hc : HasMFDerivAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.snd (curveAt Vsusp hcomplete p u)
        (ContinuousLinearMap.snd ℝ (TangentSpace I (curveAt Vsusp hcomplete p u).1)
          (TangentSpace 𝓘(ℝ, ℝ) (curveAt Vsusp hcomplete p u).2) :
          TangentSpace (I.prod 𝓘(ℝ, ℝ)) (curveAt Vsusp hcomplete p u) →L[ℝ]
          TangentSpace 𝓘(ℝ, ℝ) (curveAt Vsusp hcomplete p u).2) := by
      exact hasMFDerivAt_snd (x := curveAt Vsusp hcomplete p u)
    have hγu : HasMFDerivAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (curveAt Vsusp hcomplete p) u
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Vsusp (curveAt Vsusp hcomplete p u))) := by
      exact curveAt_integralCurve Vsusp hcomplete p u
    have hcomp := hc.comp u hγu
    rw [hasMFDerivAt_iff_hasFDerivAt] at hcomp
    have hderiv_eq : (ContinuousLinearMap.snd ℝ (TangentSpace I (curveAt Vsusp hcomplete p u).1)
          (TangentSpace 𝓘(ℝ, ℝ) (curveAt Vsusp hcomplete p u).2)).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Vsusp (curveAt Vsusp hcomplete p u))) =
        (1 : ℝ →L[ℝ] ℝ).smulRight (β (curveAt Vsusp hcomplete p u)) := by
      apply ContinuousLinearMap.ext
      intro z
      change (z • Vsusp (curveAt Vsusp hcomplete p u)).2 = z • β (curveAt Vsusp hcomplete p u)
      change (z • (χs (curveAt Vsusp hcomplete p u) • w (curveAt Vsusp hcomplete p u).1
            (curveAt Vsusp hcomplete p u).2,
          ρ (curveAt Vsusp hcomplete p u) * χt (curveAt Vsusp hcomplete p u).2)).2 =
        z • β (curveAt Vsusp hcomplete p u)
      simp [β]
    have hcomp' : HasFDerivAt (fun t : ℝ => (curveAt Vsusp hcomplete p t).2)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (β (curveAt Vsusp hcomplete p u))) u := by
      exact hcomp.congr_fderiv hderiv_eq
    exact hcomp'.hasMFDerivAt
  have hsderiv : ∀ (p : M × ℝ) (u : ℝ),
      deriv (fun t : ℝ => (curveAt Vsusp hcomplete p t).2) u = β (curveAt Vsusp hcomplete p u) := by
    intro p u
    have hd := hsnd_deriv p u
    rw [hasMFDerivAt_iff_hasFDerivAt] at hd
    rw [hd.hasDerivAt.deriv]
    change (1 : ℝ) • β (curveAt Vsusp hcomplete p u) = β (curveAt Vsusp hcomplete p u)
    simp
  have hs01 : ∀ (x : M) (u : ℝ), u ∈ Set.Icc 0 1 →
      (curveAt Vsusp hcomplete (x, 0) u).2 ∈ Set.Icc 0 1 := by
    intro x u hu
    let s : ℝ → ℝ := fun t => (curveAt Vsusp hcomplete (x, 0) t).2
    apply snd_range_of_deriv_unit (s := s)
    · intro t ht
      exact (hsnd_deriv (x, 0) t).hasFDerivAt.differentiableAt.differentiableWithinAt
    · dsimp [s]
      rw [curveAt_zero Vsusp hcomplete (x, 0)]
    · intro t ht
      rw [hsderiv (x, 0) t]
      dsimp [β]
      constructor
      · exact mul_nonneg (hρ01 (curveAt Vsusp hcomplete (x, 0) t)).1
          (hχt_ge0 (curveAt Vsusp hcomplete (x, 0) t).2)
      · exact mul_le_one₀ (hρ01 (curveAt Vsusp hcomplete (x, 0) t)).2
          (hχt_ge0 (curveAt Vsusp hcomplete (x, 0) t).2)
          (hχt_le1 (curveAt Vsusp hcomplete (x, 0) t).2)
    · exact hu
  have hA_inv_fwd : ∀ (x : M), x ∈ A → ∀ t : ℝ, t ∈ Set.Icc 0 1 →
      (curveAt Vsusp hcomplete (x, 0) t).1 ∈ A := by
    intro x hxA t ht
    exact (orbit_spatial_mem_projection (I := I) (χs := χs) (ρ := ρ) (χt := χt) (w := w)
      (Vsusp := Vsusp) (hχs_sm := hχs_sm) (hχs_supp := hχs_supp) (hρ_sm := hρ_sm)
      (hχt_sm := hχt_sm) (hχt_supp := hχt_supp) (hVsusp := hVsusp) (hVsuspsec := hVsuspsec)
      (hcomplete := hcomplete) x 0 hxA).1 t ht
  have hA_inv_back : ∀ (y : M), y ∈ A → ∀ t : ℝ, t ∈ Set.Icc (-1) 0 →
      (curveAt Vsusp hcomplete (y, 1) t).1 ∈ A := by
    intro y hyA t ht
    exact (orbit_spatial_mem_projection (I := I) (χs := χs) (ρ := ρ) (χt := χt) (w := w)
      (Vsusp := Vsusp) (hχs_sm := hχs_sm) (hχs_supp := hχs_supp) (hρ_sm := hρ_sm)
      (hχt_sm := hχt_sm) (hχt_supp := hχt_supp) (hVsusp := hVsusp) (hVsuspsec := hVsuspsec)
      (hcomplete := hcomplete) y 1 hyA).2 t ht
  have hΦsm : ContMDiff I I (↑(⊤ : ℕ∞) : WithTop ℕ∞) Φ := by
    intro x₀
    have hpair : ContMDiffAt I (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ℝ))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : M => ((1 : ℝ), (x, (0 : ℝ)))) x₀ := by
      exact ContMDiffAt.prodMk (contMDiffAt_const (c := (1 : ℝ)) (x := x₀))
        (ContMDiffAt.prodMk (contMDiffAt_id (x := x₀)) (contMDiffAt_const (c := (0 : ℝ)) (x := x₀)))
    have hc := (hflowsm (1, (x₀, (0 : ℝ)))).comp x₀ hpair
    have hfst : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : M × ℝ => p.1) (curveAt Vsusp hcomplete (x₀, 0) 1) := contMDiffAt_fst
    have hΦat : ContMDiffAt I I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : M => (curveAt Vsusp hcomplete (x, 0) 1).1) x₀ := by
      have hc' : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : M => curveAt Vsusp hcomplete (x, 0) 1) x₀ := by
        simpa [Function.comp_def] using hc
      exact hfst.comp x₀ hc'
    simpa [Φ] using hΦat
  have hΨsm : ContMDiff I I (↑(⊤ : ℕ∞) : WithTop ℕ∞) Ψ := by
    intro y₀
    have hpair : ContMDiffAt I (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ℝ))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : M => ((-1 : ℝ), (y, (1 : ℝ)))) y₀ := by
      exact ContMDiffAt.prodMk (contMDiffAt_const (c := (-1 : ℝ)) (x := y₀))
        (ContMDiffAt.prodMk (contMDiffAt_id (x := y₀)) (contMDiffAt_const (c := (1 : ℝ)) (x := y₀)))
    have hc := (hflowsm (-1, (y₀, (1 : ℝ)))).comp y₀ hpair
    have hfst : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : M × ℝ => p.1) (curveAt Vsusp hcomplete (y₀, 1) (-1)) := contMDiffAt_fst
    have hΨat : ContMDiffAt I I (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : M => (curveAt Vsusp hcomplete (y, 1) (-1)).1) y₀ := by
      have hc' : ContMDiffAt I (I.prod 𝓘(ℝ, ℝ)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y : M => curveAt Vsusp hcomplete (y, 1) (-1)) y₀ := by
        simpa [Function.comp_def] using hc
      exact hfst.comp y₀ hc'
    simpa [Ψ] using hΨat
  have hVsuspdf : ∀ q ∈ K, (NormedSpace.fromTangentSpace (F q.1 q.2))
      ((mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun x : M × ℝ => F x.1 x.2) q)
        (Vsusp q)) = 0 := by
    intro q hq
    have hdF : (NormedSpace.fromTangentSpace (F q.1 q.2))
        ((mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x q.2) q.1) (V q.1 q.2)) = -1 :=
      hVdf q hq
    have hlev := suspension_level_equation (I := I) F hF q.1 q.2
      (χs q • w q.1 q.2) (β q)
    have hwdef : w q.1 q.2 = ((fderiv ℝ (fun t : ℝ => F q.1 t) q.2) 1) • V q.1 q.2 := rfl
    have hterm1 : (mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x q.2) q.1) (χs q • w q.1 q.2) =
        -((fderiv ℝ (fun t : ℝ => F q.1 t) q.2) 1) * χs q := by
      rw [hwdef]
      rw [smul_smul]
      rw [map_smul]
      have hcast : (mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x q.2) q.1) (V q.1 q.2) = -1 := by
        change (NormedSpace.fromTangentSpace (F q.1 q.2))
          ((mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x q.2) q.1) (V q.1 q.2)) = -1
        exact hdF
      rw [hcast]
      have hsmul : (χs q * (fderiv ℝ (fun t : ℝ => F q.1 t) q.2) 1) •
          (-1 : TangentSpace 𝓘(ℝ, ℝ) (F q.1 q.2)) =
          -((χs q * (fderiv ℝ (fun t : ℝ => F q.1 t) q.2) 1) :
            TangentSpace 𝓘(ℝ, ℝ) (F q.1 q.2)) := by
        calc
          (χs q * (fderiv ℝ (fun t : ℝ => F q.1 t) q.2) 1) •
              (-1 : TangentSpace 𝓘(ℝ, ℝ) (F q.1 q.2))
              = -((χs q * (fderiv ℝ (fun t : ℝ => F q.1 t) q.2) 1) •
                  (1 : TangentSpace 𝓘(ℝ, ℝ) (F q.1 q.2))) := by
                rw [smul_neg]
          _ = -((χs q * (fderiv ℝ (fun t : ℝ => F q.1 t) q.2) 1) :
              TangentSpace 𝓘(ℝ, ℝ) (F q.1 q.2)) := by
                congr 1
                change (χs q * (fderiv ℝ (fun t : ℝ => F q.1 t) q.2) 1) • (1 : ℝ) =
                  (χs q * (fderiv ℝ (fun t : ℝ => F q.1 t) q.2) 1 : ℝ)
                rw [smul_eq_mul]
                ring
      rw [hsmul]
      ring_nf
    have hlev' : (NormedSpace.fromTangentSpace (F q.1 q.2))
        ((mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun x : M × ℝ => F x.1 x.2) q) (Vsusp q)) =
        (NormedSpace.fromTangentSpace (F q.1 q.2))
          ((mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x q.2) q.1) (χs q • w q.1 q.2)) +
        ((fderiv ℝ (fun t : ℝ => F q.1 t) q.2) 1) * β q := by
      dsimp [Vsusp]
      exact hlev
    rw [hlev']
    have hval1 : (NormedSpace.fromTangentSpace (F q.1 q.2))
        ((mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x q.2) q.1) (χs q • w q.1 q.2)) =
        -((fderiv ℝ (fun t : ℝ => F q.1 t) q.2) 1) * χs q := by
      change (mfderiv I 𝓘(ℝ, ℝ) (fun x : M => F x q.2) q.1) (χs q • w q.1 q.2) =
        -((fderiv ℝ (fun t : ℝ => F q.1 t) q.2) 1) * χs q
      exact hterm1
    rw [hval1]
    have hχs1 : χs q = 1 := hχsK q hq
    have hβ1 : β q = 1 := by
      dsimp [β]
      have hρ1 : ρ q = 1 := hρ_SA q (by
        exact ⟨hK1subA ⟨q, hq, rfl⟩, by constructor <;> linarith [hq.2.1, hq.2.2]⟩)
      have hχt1 : χt q.2 = 1 := hχt_one q.2 hq.2
      rw [hρ1, hχt1]
      norm_num
    rw [hχs1, hβ1]
    ring
  have hDflow : ∀ x : M, x ∈ D → ∀ s₀ : ℝ, s₀ ∈ Set.Icc 0 1 →
      ∀ t : ℝ, (curveAt Vsusp hcomplete (x, s₀) t).1 = x := by
    intro x hxD s₀ hs₀ t
    rcases exists_scalar_flow_smooth_cutoff (I := I) (ρ := ρ) (χt := χt)
      hρ_sm hχt_sm hχt_supp x s₀ with ⟨τ, hτ0, hτIs⟩
    have hτIs' : IsMIntegralCurve (I := 𝓘(ℝ, ℝ)) (M := ℝ) (E := ℝ) (H := ℝ) τ
        (fun s : ℝ => (ρ (x, s) * Real.smoothTransition (2 - s) * Real.smoothTransition (s + 1) :
          TangentSpace 𝓘(ℝ, ℝ) s)) := by
      simpa [χt, mul_assoc] using hτIs
    have hτbnd : ∀ u : ℝ, τ u ∈ Set.Ioo (-1) 2 :=
      scalarFlow_rho_smoothTransition_bounds (I := I) (ρ := ρ) hρ_sm hs₀ hτ0 hτIs'
    let c : ℝ → M × ℝ := fun u => (x, τ u)
    have hcIs : IsMIntegralCurve c Vsusp := by
      intro u
      have hτ' : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) τ u
          ((1 : ℝ →L[ℝ] ℝ).smulRight (ρ (x, τ u) * χt (τ u))) := hτIs u
      have hpair : HasMFDerivAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) c u
          ((0 : TangentSpace 𝓘(ℝ, ℝ) u →L[ℝ] TangentSpace I x).prod
            ((1 : ℝ →L[ℝ] ℝ).smulRight (ρ (x, τ u) * χt (τ u)))) := by
        simpa [c] using (hasMFDerivAt_const (c := x) (x := u)).prodMk hτ'
      have hV : Vsusp (c u) = (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) (c u) from
          (χs (c u) • w x (τ u), ρ (c u) * χt (τ u))) := by
        rw [hVsusp]
      have hχs0 : χs (c u) = 0 := hχsD x hxD (τ u) (hτbnd u)
      have hderiv_eq : (0 : TangentSpace 𝓘(ℝ, ℝ) u →L[ℝ] TangentSpace I x).prod
          ((1 : ℝ →L[ℝ] ℝ).smulRight (ρ (x, τ u) * χt (τ u))) =
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Vsusp (c u))) := by
        apply ContinuousLinearMap.ext_ring
        change ((0 : TangentSpace 𝓘(ℝ, ℝ) u →L[ℝ] TangentSpace I x) (1 : ℝ),
            ((1 : ℝ →L[ℝ] ℝ).smulRight (ρ (x, τ u) * χt (τ u))) (1 : ℝ)) =
          ((1 : ℝ →L[ℝ] ℝ) (1 : ℝ) • Vsusp (c u))
        rw [hV]
        rw [hχs0]
        simp [ContinuousLinearMap.smulRight_apply, smul_eq_mul]
        rfl
      exact hpair.congr_mfderiv hderiv_eq
    have heq : curveAt Vsusp hcomplete (x, s₀) = c := by
      exact isMIntegralCurve_eq_of_contMDiff (t₀ := 0)
        (I := I.prod 𝓘(ℝ, ℝ)) (v := Vsusp) (γ := curveAt Vsusp hcomplete (x, s₀)) (γ' := c)
        (hv := hVsuspsec.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞))
        (fun u => BoundarylessManifold.isInteriorPoint (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ)
          (x := curveAt Vsusp hcomplete (x, s₀) u))
        (curveAt_integralCurve Vsusp hcomplete (x, s₀)) hcIs
        (by
          dsimp [c]
          rw [hτ0, curveAt_zero Vsusp hcomplete (x, s₀)])
    change (curveAt Vsusp hcomplete (x, s₀) t).1 = x
    simpa [c] using congrArg Prod.fst (congrFun heq t)
  have hDfixprop : ∀ x : M, x ∈ D → Φ x = x ∧ Ψ x = x := by
    intro x hxD
    constructor
    · dsimp [Φ]
      exact hDflow x hxD 0 (by norm_num) 1
    · dsimp [Ψ]
      exact hDflow x hxD 1 (by norm_num) (-1)
  have hf_sm : ∀ x : M, DifferentiableOn ℝ (fun t : ℝ =>
      F (curveAt Vsusp hcomplete (x, 0) t).1 (curveAt Vsusp hcomplete (x, 0) t).2) Set.univ := by
    intro x t ht
    have hpair : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ℝ))) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : ℝ => (u, (x, (0 : ℝ)))) t := by
      exact ContMDiffAt.prodMk (contMDiffAt_id (x := t)) (contMDiffAt_const (c := (x, (0 : ℝ))) (x := t))
    have hflowAt : ContMDiffAt (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ℝ))) (I.prod 𝓘(ℝ, ℝ)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × (M × ℝ) => curveAt Vsusp hcomplete p.2 p.1) (t, (x, 0)) := hflowsm (t, (x, 0))
    have hγat : ContMDiffAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : ℝ => curveAt Vsusp hcomplete (x, 0) u) t := by
      simpa [Function.comp_def] using hflowAt.comp t hpair
    have hfAt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : ℝ => F (curveAt Vsusp hcomplete (x, 0) u).1 (curveAt Vsusp hcomplete (x, 0) u).2) t := by
      have hc := (hF (curveAt Vsusp hcomplete (x, 0) t)).comp t hγat
      simpa [Function.comp_def] using hc
    have hmdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun u : ℝ => F (curveAt Vsusp hcomplete (x, 0) u).1 (curveAt Vsusp hcomplete (x, 0) u).2) t :=
      hfAt.mdifferentiableAt (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
    exact hmdiff.hasMFDerivAt.hasFDerivAt.differentiableAt.differentiableWithinAt
  have hf_deriv0 : ∀ (x : M) (t : ℝ), t ∈ Set.Icc 0 1 →
      F (curveAt Vsusp hcomplete (x, 0) t).1 (curveAt Vsusp hcomplete (x, 0) t).2 ∈
        Set.Icc (-(2 * ε₀)) (2 * ε₀) →
      deriv (fun u : ℝ => F (curveAt Vsusp hcomplete (x, 0) u).1 (curveAt Vsusp hcomplete (x, 0) u).2) t = 0 := by
    intro x t ht hft
    have hcomp := (hF (curveAt Vsusp hcomplete (x, 0) t)).mdifferentiableAt (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0) |>.hasMFDerivAt.comp t (curveAt_integralCurve Vsusp hcomplete (x, 0) t)
    have hd : deriv (fun u : ℝ => F (curveAt Vsusp hcomplete (x, 0) u).1 (curveAt Vsusp hcomplete (x, 0) u).2) t =
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : M × ℝ => F q.1 q.2) (curveAt Vsusp hcomplete (x, 0) t)) (Vsusp (curveAt Vsusp hcomplete (x, 0) t)) := by
      have hfd : HasFDerivAt (fun u : ℝ => F (curveAt Vsusp hcomplete (x, 0) u).1 (curveAt Vsusp hcomplete (x, 0) u).2)
          ((mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : M × ℝ => F q.1 q.2) (curveAt Vsusp hcomplete (x, 0) t)).comp
            ((1 : ℝ →L[ℝ] ℝ).smulRight (Vsusp (curveAt Vsusp hcomplete (x, 0) t)))) t := hcomp.hasFDerivAt
      rw [hfd.hasDerivAt.deriv]
      change (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : M × ℝ => F q.1 q.2) (curveAt Vsusp hcomplete (x, 0) t))
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Vsusp (curveAt Vsusp hcomplete (x, 0) t)) 1) =
        (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : M × ℝ => F q.1 q.2) (curveAt Vsusp hcomplete (x, 0) t)) (Vsusp (curveAt Vsusp hcomplete (x, 0) t))
      simp
    rw [hd]
    have hs01t : (curveAt Vsusp hcomplete (x, 0) t).2 ∈ Set.Icc 0 1 := hs01 x t ht
    have hKmem : curveAt Vsusp hcomplete (x, 0) t ∈ K := ⟨abs_le.mpr ⟨hft.1, hft.2⟩, hs01t⟩
    have hzero : (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : M × ℝ => F q.1 q.2) (curveAt Vsusp hcomplete (x, 0) t)) (Vsusp (curveAt Vsusp hcomplete (x, 0) t)) = 0 := by
      exact hVsuspdf (curveAt Vsusp hcomplete (x, 0) t) hKmem
    exact hzero
  have hFconst : ∀ (x : M) (u : ℝ), u ∈ Set.Icc 0 1 →
      F x 0 ∈ Set.Ioo (-(2 * ε₀)) (2 * ε₀) →
      F (curveAt Vsusp hcomplete (x, 0) u).1 (curveAt Vsusp hcomplete (x, 0) u).2 = F x 0 := by
    intro x u hu hval0
    have hmain : (fun t : ℝ => F (curveAt Vsusp hcomplete (x, 0) t).1 (curveAt Vsusp hcomplete (x, 0) t).2) u =
        (fun t : ℝ => F (curveAt Vsusp hcomplete (x, 0) t).1 (curveAt Vsusp hcomplete (x, 0) t).2) 0 :=
      sublevel_const_of_deriv_eq_zero_on_unit (hf_sm x) (by positivity : (0 : ℝ) < 2 * ε₀)
        (by simpa [curveAt_zero Vsusp hcomplete (x, 0)] using hval0) (hf_deriv0 x) u hu
    change F (curveAt Vsusp hcomplete (x, 0) u).1 (curveAt Vsusp hcomplete (x, 0) u).2 = F x 0
    simpa [curveAt_zero Vsusp hcomplete (x, 0)] using hmain
  have hs1 : ∀ (x : M), x ∈ A → (curveAt Vsusp hcomplete (x, 0) 1).2 = 1 := by
    intro x hxA
    let s : ℝ → ℝ := fun t => (curveAt Vsusp hcomplete (x, 0) t).2
    apply eq_self_of_deriv_one_on_unit (φ := s)
    · intro t ht
      exact (hsnd_deriv (x, 0) t).hasFDerivAt.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [hsderiv (x, 0) t]
      dsimp [β]
      have hAt : (curveAt Vsusp hcomplete (x, 0) t).1 ∈ A := hA_inv_fwd x hxA t ht
      have hs01t : (curveAt Vsusp hcomplete (x, 0) t).2 ∈ Set.Icc 0 1 := hs01 x t ht
      have hSA : curveAt Vsusp hcomplete (x, 0) t ∈ SA := ⟨hAt,
        by constructor <;> linarith [hs01t.1, hs01t.2]⟩
      have hρ1 : ρ (curveAt Vsusp hcomplete (x, 0) t) = 1 := hρ_SA _ hSA
      have hχt1 : χt (curveAt Vsusp hcomplete (x, 0) t).2 = 1 := hχt_one _ hs01t
      rw [hρ1, hχt1]
      norm_num
    · dsimp [s]
      rw [curveAt_zero Vsusp hcomplete (x, 0)]
  have houtside_orbit_const : ∀ (x : M), x ∉ A → ∀ s₀ : ℝ, ∀ t : ℝ,
      (curveAt Vsusp hcomplete (x, s₀) t).1 = x := by
    intro x hxA s₀ t
    rcases exists_scalar_flow_smooth_cutoff (I := I) (ρ := ρ) (χt := χt)
      hρ_sm hχt_sm hχt_supp x s₀ with ⟨τ, hτ0, hτIs⟩
    let c : ℝ → M × ℝ := fun u => (x, τ u)
    have hcIs : IsMIntegralCurve c Vsusp := by
      exact pairFlow_aux_curve_integral (I := I) (Vsusp := Vsusp) (hVsusp := hVsusp)
        (τ := τ) (hτIs := hτIs) (hχs := fun s => hχs_out (x, s) hxA)
    have heq : curveAt Vsusp hcomplete (x, s₀) = c := by
      exact isMIntegralCurve_eq_of_contMDiff (t₀ := 0)
        (I := I.prod 𝓘(ℝ, ℝ)) (v := Vsusp) (γ := curveAt Vsusp hcomplete (x, s₀)) (γ' := c)
        (hv := hVsuspsec.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞))
        (fun u => BoundarylessManifold.isInteriorPoint (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ)
          (x := curveAt Vsusp hcomplete (x, s₀) u))
        (curveAt_integralCurve Vsusp hcomplete (x, s₀)) hcIs
        (by
          dsimp [c]
          rw [hτ0, curveAt_zero Vsusp hcomplete (x, s₀)])
    change (curveAt Vsusp hcomplete (x, s₀) t).1 = x
    simpa [c] using congrArg Prod.fst (congrFun heq t)
  have houtside_strip_abs : ∀ x : M, x ∉ Prod.fst '' K → ∀ s : ℝ, s ∈ Set.Icc 0 1 → 2 * ε₀ < |F x s| := by
    intro x hx s hs
    by_contra hle
    have habs : |F x s| ≤ 2 * ε₀ := le_of_not_gt hle
    exact hx ⟨(x, s), ⟨habs, hs⟩, rfl⟩
  have hsign_outside : ∀ x : M, x ∉ Prod.fst '' K → (F x 0 ≤ 0 ↔ F x 1 ≤ 0) := by
    intro x hx
    have hne : ∀ s : ℝ, s ∈ Set.Icc 0 1 → F x s ≠ 0 := by
      intro s hs
      exact (abs_pos.mp (lt_trans (mul_pos (by norm_num) hε₀) (houtside_strip_abs x hx s hs)))
    exact sublevel_sign_agreement_of_no_zero
      (by
        have hc : Continuous (fun s : ℝ => F x s) :=
          hF.continuous.comp (continuous_const.prodMk continuous_id)
        exact hc.continuousOn)
      hne
  have hsub_fwd : ∀ x : M, F x 0 ≤ 0 → F (Φ x) 1 ≤ 0 := by
    intro x hx
    by_cases hxD : x ∈ D
    · have hfix := (hDfixprop x hxD).1
      rw [hfix]
      exact (hDsign x hxD).1 hx
    · by_cases hdeep : F x 0 ≤ -(2 * ε₀)
      · by_cases hxA : x ∈ A
        · have hb : (fun t : ℝ => F (curveAt Vsusp hcomplete (x, 0) t).1 (curveAt Vsusp hcomplete (x, 0) t).2) 1 ≤
              -(2 * ε₀) :=
            sublevel_const_of_deriv_eq_zero_below (hf_sm x) (by positivity : (0 : ℝ) < 2 * ε₀)
              (by simpa [curveAt_zero Vsusp hcomplete (x, 0)] using hdeep) (hf_deriv0 x)
              (t₁ := (1 : ℝ)) (by norm_num)
          have hγ1 : curveAt Vsusp hcomplete (x, 0) 1 = (Φ x, 1) := by
            ext <;> simp [Φ, hs1 x hxA]
          have hΦ : F (Φ x) 1 ≤ -(2 * ε₀) := by
            change (fun q : M × ℝ => F q.1 q.2) (Φ x, 1) ≤ -(2 * ε₀)
            rw [← hγ1]
            simpa using hb
          exact le_trans hΦ (by linarith [hε₀])
        · have hxK : x ∉ Prod.fst '' K := by
            intro hmem
            exact hxA (hK1subA hmem)
          have hfix := houtside_orbit_const x hxA 0 1
          change F ((curveAt Vsusp hcomplete (x, 0) 1).1) 1 ≤ 0
          rw [hfix]
          exact (hsign_outside x hxK).1 hx
      · have hval0 : F x 0 ∈ Set.Ioo (-(2 * ε₀)) (2 * ε₀) := by
          constructor
          · exact lt_of_not_ge hdeep
          · exact lt_of_le_of_lt hx (by linarith [hε₀])
        have hxA : x ∈ A := hK1subA ⟨(x, 0), ⟨abs_le.mpr ⟨le_of_lt hval0.1, le_of_lt hval0.2⟩, by norm_num⟩, rfl⟩
        have hconst := hFconst x 1 (by norm_num) hval0
        have hγ1 : curveAt Vsusp hcomplete (x, 0) 1 = (Φ x, 1) := by
          ext <;> simp [Φ, hs1 x hxA]
        have hΦ : F (Φ x) 1 = F x 0 := by
          change (fun q : M × ℝ => F q.1 q.2) (Φ x, 1) = F x 0
          rw [← hγ1]
          exact hconst
        rw [hΦ]
        exact hx
  have hbnd_fwd : ∀ x : M, F x 0 = 0 → F (Φ x) 1 = 0 := by
    intro x hx
    have hval0 : F x 0 ∈ Set.Ioo (-(2 * ε₀)) (2 * ε₀) := by
      rw [hx]
      constructor <;> linarith [hε₀]
    have hxA : x ∈ A := hK1subA ⟨(x, 0), ⟨abs_le.mpr ⟨le_of_lt hval0.1, le_of_lt hval0.2⟩, by norm_num⟩, rfl⟩
    have hconst := hFconst x 1 (by norm_num) hval0
    have hγ1 : curveAt Vsusp hcomplete (x, 0) 1 = (Φ x, 1) := by
      ext <;> simp [Φ, hs1 x hxA]
    have hΦ : F (Φ x) 1 = F x 0 := by
      change (fun q : M × ℝ => F q.1 q.2) (Φ x, 1) = F x 0
      rw [← hγ1]
      exact hconst
    rw [hΦ]
    exact hx
  have hstrict_fwd : ∀ x : M, F x 0 < 0 → F (Φ x) 1 < 0 := by
    intro x hx
    by_cases hxD : x ∈ D
    · have hfix := (hDfixprop x hxD).1
      rw [hfix]
      have hle : F x 1 ≤ 0 := (hDsign x hxD).1 (le_of_lt hx)
      have hne : F x 1 ≠ 0 := by
        intro hzero
        have hsep := hDsep x hxD 1 (by norm_num)
        rw [hzero] at hsep
        have hsep' : 2 * ε₀ < 0 := by simpa using hsep
        nlinarith [hε₀, hsep']
      exact lt_of_le_of_ne hle hne
    · by_cases hdeep : F x 0 ≤ -(2 * ε₀)
      · by_cases hxA : x ∈ A
        · have hb : (fun t : ℝ => F (curveAt Vsusp hcomplete (x, 0) t).1 (curveAt Vsusp hcomplete (x, 0) t).2) 1 ≤
              -(2 * ε₀) :=
            sublevel_const_of_deriv_eq_zero_below (hf_sm x) (by positivity : (0 : ℝ) < 2 * ε₀)
              (by simpa [curveAt_zero Vsusp hcomplete (x, 0)] using hdeep) (hf_deriv0 x)
              (t₁ := (1 : ℝ)) (by norm_num)
          have hγ1 : curveAt Vsusp hcomplete (x, 0) 1 = (Φ x, 1) := by
            ext <;> simp [Φ, hs1 x hxA]
          have hΦ : F (Φ x) 1 ≤ -(2 * ε₀) := by
            change (fun q : M × ℝ => F q.1 q.2) (Φ x, 1) ≤ -(2 * ε₀)
            rw [← hγ1]
            simpa using hb
          exact lt_of_le_of_lt hΦ (by linarith [hε₀])
        · have hxK : x ∉ Prod.fst '' K := by
            intro hmem
            exact hxA (hK1subA hmem)
          have hfix := houtside_orbit_const x hxA 0 1
          change F ((curveAt Vsusp hcomplete (x, 0) 1).1) 1 < 0
          rw [hfix]
          have hle : F x 1 ≤ 0 := (hsign_outside x hxK).1 (le_of_lt hx)
          have hne : F x 1 ≠ 0 := by
            intro hzero
            have habs := houtside_strip_abs x hxK 1 (by norm_num)
            rw [hzero] at habs
            have habs' : 2 * ε₀ < 0 := by simpa using habs
            nlinarith [hε₀, habs']
          exact lt_of_le_of_ne hle hne
      · have hval0 : F x 0 ∈ Set.Ioo (-(2 * ε₀)) (2 * ε₀) := by
          constructor
          · exact lt_of_not_ge hdeep
          · exact lt_trans hx (by linarith [hε₀])
        have hxA : x ∈ A := hK1subA ⟨(x, 0), ⟨abs_le.mpr ⟨le_of_lt hval0.1, le_of_lt hval0.2⟩, by norm_num⟩, rfl⟩
        have hconst := hFconst x 1 (by norm_num) hval0
        have hγ1 : curveAt Vsusp hcomplete (x, 0) 1 = (Φ x, 1) := by
          ext <;> simp [Φ, hs1 x hxA]
        have hΦ : F (Φ x) 1 = F x 0 := by
          change (fun q : M × ℝ => F q.1 q.2) (Φ x, 1) = F x 0
          rw [← hγ1]
          exact hconst
        rw [hΦ]
        exact hx
  have hinv_fwd : ∀ x : M, F x 0 ≤ 0 → Ψ (Φ x) = x := by
    intro x hx
    by_cases hxA : x ∈ A
    · have hγ1 : curveAt Vsusp hcomplete (x, 0) 1 = (Φ x, 1) := by
        ext <;> simp [Φ, hs1 x hxA]
      have hγ0 : curveAt Vsusp hcomplete (x, 0) 0 = (x, 0) := curveAt_zero Vsusp hcomplete (x, 0)
      have hgrp : curveAt Vsusp hcomplete (curveAt Vsusp hcomplete (x, 0) 1) (-1) = curveAt Vsusp hcomplete (x, 0) 0 := by
        rw [← curveAt_add Vsusp (hVsuspsec.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)) hcomplete (x, 0) 1 (-1)]
        norm_num
      rw [hγ1] at hgrp
      rw [hγ0] at hgrp
      dsimp [Ψ]
      simpa using congrArg Prod.fst hgrp
    · have hfx : Φ x = x := houtside_orbit_const x hxA 0 1
      have hfy : Ψ x = x := houtside_orbit_const x hxA 1 (-1)
      rw [hfx, hfy]
  have hsback : ∀ (y : M) (u : ℝ), u ∈ Set.Icc 0 1 →
      (curveAt Vsusp hcomplete (y, 1) (-u)).2 ∈ Set.Icc 0 1 := by
    intro y u hu
    let s : ℝ → ℝ := fun t => 1 - (curveAt Vsusp hcomplete (y, 1) (-t)).2
    have hs0 : s 0 = 0 := by
      dsimp [s]
      norm_num
      rw [curveAt_zero Vsusp hcomplete (y, 1)]
      norm_num
    have hsd : ∀ t : ℝ, t ∈ Set.Icc 0 1 → deriv s t ∈ Set.Icc 0 1 := by
      intro t ht
      have hdneg : deriv (fun v : ℝ => (curveAt Vsusp hcomplete (y, 1) (-v)).2) t =
          -deriv (fun v : ℝ => (curveAt Vsusp hcomplete (y, 1) v).2) (-t) := by
        exact deriv_comp_neg (f := fun v : ℝ => (curveAt Vsusp hcomplete (y, 1) v).2) (x := t)
      have hdcomp : deriv s t = -deriv (fun v : ℝ => (curveAt Vsusp hcomplete (y, 1) (-v)).2) t := by
        dsimp [s]
        rw [deriv_const_sub (c := (1 : ℝ))
          (f := fun v : ℝ => (curveAt Vsusp hcomplete (y, 1) (-v)).2)]
      rw [hdcomp, hdneg]
      rw [hsderiv (y, 1) (-t)]
      have hβ01 : β (curveAt Vsusp hcomplete (y, 1) (-t)) ∈ Set.Icc 0 1 := by
        dsimp [β]
        constructor
        · exact mul_nonneg (hρ01 (curveAt Vsusp hcomplete (y, 1) (-t))).1
            (hχt_ge0 (curveAt Vsusp hcomplete (y, 1) (-t)).2)
        · exact mul_le_one₀ (hρ01 (curveAt Vsusp hcomplete (y, 1) (-t))).2
            (hχt_ge0 (curveAt Vsusp hcomplete (y, 1) (-t)).2)
            (hχt_le1 (curveAt Vsusp hcomplete (y, 1) (-t)).2)
      simpa using hβ01
    have hsmain := snd_range_of_deriv_unit (s := s) (by
      intro t ht
      have hc : DifferentiableWithinAt ℝ (fun t : ℝ => (curveAt Vsusp hcomplete (y, 1) t).2) univ (-t) :=
        (hsnd_deriv (y, 1) (-t)).hasFDerivAt.differentiableAt.differentiableWithinAt (s := univ)
      have hneg : DifferentiableWithinAt ℝ (fun v : ℝ => -v) univ t := differentiableWithinAt_id.neg
      have hsub : MapsTo (fun v : ℝ => -v) univ univ := by intro z hz; trivial
      have hcomp : DifferentiableWithinAt ℝ (fun v : ℝ => (curveAt Vsusp hcomplete (y, 1) (-v)).2) univ t :=
        DifferentiableWithinAt.comp (𝕜 := ℝ) (E := ℝ) (F := ℝ) (G := ℝ)
          (f := fun v : ℝ => -v) (g := fun t : ℝ => (curveAt Vsusp hcomplete (y, 1) t).2)
          (s := univ) (t := univ) t hc hneg hsub
      exact DifferentiableWithinAt.sub (differentiableWithinAt_const (c := (1 : ℝ)) (x := t)) hcomp
      ) hs0 hsd u hu
    have hs01u : s u ∈ Set.Icc 0 1 := hsmain
    dsimp [s] at hs01u
    constructor
    · linarith [hs01u.2]
    · linarith [hs01u.1]
  have hf_back_sm : ∀ y : M, DifferentiableOn ℝ (fun t : ℝ =>
      F (curveAt Vsusp hcomplete (y, 1) (-t)).1 (curveAt Vsusp hcomplete (y, 1) (-t)).2) Set.univ := by
    intro y t ht
    have hcomp := (hF (curveAt Vsusp hcomplete (y, 1) (-t))).mdifferentiableAt (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0) |>.hasMFDerivAt.comp (-t) (curveAt_integralCurve Vsusp hcomplete (y, 1) (-t))
    have hneg : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => -s) t (-1 : ℝ →L[ℝ] ℝ) := by
      have hneg' : HasFDerivAt (fun s : ℝ => -s) (-1 : ℝ →L[ℝ] ℝ) t := by
        exact (hasFDerivAt_id t).neg
      exact hneg'.hasMFDerivAt
    exact (hcomp.comp t hneg).hasFDerivAt.differentiableAt.differentiableWithinAt
  have hf_back_deriv0 : ∀ (y : M) (t : ℝ), t ∈ Set.Icc 0 1 →
      F (curveAt Vsusp hcomplete (y, 1) (-t)).1 (curveAt Vsusp hcomplete (y, 1) (-t)).2 ∈
        Set.Icc (-(2 * ε₀)) (2 * ε₀) →
      deriv (fun u : ℝ => F (curveAt Vsusp hcomplete (y, 1) (-u)).1 (curveAt Vsusp hcomplete (y, 1) (-u)).2) t = 0 := by
    intro y t ht hft
    have hcomp := (hF (curveAt Vsusp hcomplete (y, 1) (-t))).mdifferentiableAt (by norm_num : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0) |>.hasMFDerivAt.comp (-t) (curveAt_integralCurve Vsusp hcomplete (y, 1) (-t))
    have hd : deriv (fun u : ℝ => F (curveAt Vsusp hcomplete (y, 1) (-u)).1 (curveAt Vsusp hcomplete (y, 1) (-u)).2) t =
        -(mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : M × ℝ => F q.1 q.2) (curveAt Vsusp hcomplete (y, 1) (-t))) (Vsusp (curveAt Vsusp hcomplete (y, 1) (-t))) := by
      have hneg : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => -s) t (-1 : ℝ →L[ℝ] ℝ) := by
        exact (hasFDerivAt_id t).neg |>.hasMFDerivAt
      have hchain := hcomp.comp t hneg
      have hfd : HasFDerivAt (fun u : ℝ => F (curveAt Vsusp hcomplete (y, 1) (-u)).1 (curveAt Vsusp hcomplete (y, 1) (-u)).2)
          (((mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : M × ℝ => F q.1 q.2) (curveAt Vsusp hcomplete (y, 1) (-t))).comp
            ((1 : ℝ →L[ℝ] ℝ).smulRight (Vsusp (curveAt Vsusp hcomplete (y, 1) (-t))))).comp (-1 : ℝ →L[ℝ] ℝ)) t := by
        exact hchain.hasFDerivAt
      rw [hfd.hasDerivAt.deriv]
      change ((((mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : M × ℝ => F q.1 q.2) (curveAt Vsusp hcomplete (y, 1) (-t))).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Vsusp (curveAt Vsusp hcomplete (y, 1) (-t))))).comp (-1 : ℝ →L[ℝ] ℝ)) 1) =
        -(mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : M × ℝ => F q.1 q.2) (curveAt Vsusp hcomplete (y, 1) (-t))) (Vsusp (curveAt Vsusp hcomplete (y, 1) (-t)))
      simp
    rw [hd]
    have hsbackt : (curveAt Vsusp hcomplete (y, 1) (-t)).2 ∈ Set.Icc 0 1 := hsback y t ht
    have hKmem : curveAt Vsusp hcomplete (y, 1) (-t) ∈ K := ⟨abs_le.mpr ⟨hft.1, hft.2⟩, hsbackt⟩
    have hzneg : -((mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun q : M × ℝ => F q.1 q.2) (curveAt Vsusp hcomplete (y, 1) (-t))) (Vsusp (curveAt Vsusp hcomplete (y, 1) (-t)))) = 0 := by
      simpa using congrArg Neg.neg (hVsuspdf (curveAt Vsusp hcomplete (y, 1) (-t)) hKmem)
    exact hzneg
  have hFconstBack : ∀ (y : M) (u : ℝ), u ∈ Set.Icc 0 1 →
      F y 1 ∈ Set.Ioo (-(2 * ε₀)) (2 * ε₀) →
      F (curveAt Vsusp hcomplete (y, 1) (-u)).1 (curveAt Vsusp hcomplete (y, 1) (-u)).2 = F y 1 := by
    intro y u hu hval0
    have hmain : (fun t : ℝ => F (curveAt Vsusp hcomplete (y, 1) (-t)).1 (curveAt Vsusp hcomplete (y, 1) (-t)).2) u =
        (fun t : ℝ => F (curveAt Vsusp hcomplete (y, 1) (-t)).1 (curveAt Vsusp hcomplete (y, 1) (-t)).2) 0 :=
      sublevel_const_of_deriv_eq_zero_on_unit (hf_back_sm y) (by positivity : (0 : ℝ) < 2 * ε₀)
        (by simpa [curveAt_zero Vsusp hcomplete (y, 1)] using hval0) (hf_back_deriv0 y) u hu
    change F (curveAt Vsusp hcomplete (y, 1) (-u)).1 (curveAt Vsusp hcomplete (y, 1) (-u)).2 = F y 1
    simpa [curveAt_zero Vsusp hcomplete (y, 1)] using hmain
  have hsb1 : ∀ (y : M), y ∈ A → (curveAt Vsusp hcomplete (y, 1) (-1)).2 = 0 := by
    intro y hyA
    let s : ℝ → ℝ := fun t => (curveAt Vsusp hcomplete (y, 1) (-t)).2
    have hφdiff : DifferentiableOn ℝ (fun t : ℝ => 1 - s t) Set.univ := by
      intro t ht
      have hc : DifferentiableWithinAt ℝ (fun t : ℝ => (curveAt Vsusp hcomplete (y, 1) t).2) univ (-t) :=
        (hsnd_deriv (y, 1) (-t)).hasFDerivAt.differentiableAt.differentiableWithinAt (s := univ)
      have hcomp : DifferentiableWithinAt ℝ (fun v : ℝ => (curveAt Vsusp hcomplete (y, 1) (-v)).2) univ t :=
        DifferentiableWithinAt.comp (𝕜 := ℝ) (E := ℝ) (F := ℝ) (G := ℝ)
          (f := fun v : ℝ => -v) (g := fun t : ℝ => (curveAt Vsusp hcomplete (y, 1) t).2)
          (s := univ) (t := univ) t hc differentiableWithinAt_id.neg
          (by intro z hz; trivial)
      exact DifferentiableWithinAt.sub (differentiableWithinAt_const (c := (1 : ℝ)) (x := t)) hcomp
    have hφderiv : ∀ t : ℝ, t ∈ Set.Icc 0 1 → deriv (fun t : ℝ => 1 - s t) t = 1 := by
      intro t ht
      have hsd : deriv (fun t : ℝ => (curveAt Vsusp hcomplete (y, 1) (-t)).2) t =
          -β (curveAt Vsusp hcomplete (y, 1) (-t)) := by
        have hdneg : deriv (fun v : ℝ => (curveAt Vsusp hcomplete (y, 1) (-v)).2) t =
            -deriv (fun v : ℝ => (curveAt Vsusp hcomplete (y, 1) v).2) (-t) := by
          exact deriv_comp_neg (f := fun v : ℝ => (curveAt Vsusp hcomplete (y, 1) v).2) (x := t)
        rw [hdneg, hsderiv (y, 1) (-t)]
      have hd1 : deriv (fun t : ℝ => 1 - s t) t = β (curveAt Vsusp hcomplete (y, 1) (-t)) := by
        dsimp [s]
        rw [deriv_const_sub (c := (1 : ℝ))
          (f := fun t : ℝ => (curveAt Vsusp hcomplete (y, 1) (-t)).2)]
        rw [hsd]
        ring
      rw [hd1]
      dsimp [β]
      have hAt : (curveAt Vsusp hcomplete (y, 1) (-t)).1 ∈ A :=
        hA_inv_back y hyA (-t) (by constructor <;> linarith [ht.1, ht.2])
      have hsbackt : (curveAt Vsusp hcomplete (y, 1) (-t)).2 ∈ Set.Icc 0 1 := hsback y t ht
      have hSA : curveAt Vsusp hcomplete (y, 1) (-t) ∈ SA := ⟨hAt,
        by constructor <;> linarith [hsbackt.1, hsbackt.2]⟩
      have hρ1 : ρ (curveAt Vsusp hcomplete (y, 1) (-t)) = 1 := hρ_SA _ hSA
      have hχt1 : χt (curveAt Vsusp hcomplete (y, 1) (-t)).2 = 1 := hχt_one _ hsbackt
      rw [hρ1, hχt1]
      norm_num
    have hφ0 : (fun t : ℝ => 1 - s t) 0 = 0 := by
      change 1 - s 0 = 0
      dsimp [s]
      norm_num
      rw [curveAt_zero Vsusp hcomplete (y, 1)]
      norm_num
    have hφ1 : (fun t : ℝ => 1 - s t) 1 = 1 :=
      eq_self_of_deriv_one_on_unit (φ := fun t : ℝ => 1 - s t) hφdiff hφderiv hφ0
    dsimp [s] at hφ1
    linarith
  have hsub_back : ∀ y : M, F y 1 ≤ 0 → F (Ψ y) 0 ≤ 0 := by
    intro y hy
    by_cases hyD : y ∈ D
    · have hfix := (hDfixprop y hyD).2
      rw [hfix]
      exact (hDsign y hyD).2 hy
    · by_cases hdeep : F y 1 ≤ -(2 * ε₀)
      · by_cases hyA : y ∈ A
        · have hb : (fun t : ℝ => F (curveAt Vsusp hcomplete (y, 1) (-t)).1 (curveAt Vsusp hcomplete (y, 1) (-t)).2) 1 ≤
              -(2 * ε₀) :=
            sublevel_const_of_deriv_eq_zero_below (hf_back_sm y) (by positivity : (0 : ℝ) < 2 * ε₀)
              (by simpa [curveAt_zero Vsusp hcomplete (y, 1)] using hdeep) (hf_back_deriv0 y)
              (t₁ := (1 : ℝ)) (by norm_num)
          have hγ1 : curveAt Vsusp hcomplete (y, 1) (-1) = (Ψ y, 0) := by
            ext <;> simp [Ψ, hsb1 y hyA]
          have hΨ : F (Ψ y) 0 ≤ -(2 * ε₀) := by
            change (fun q : M × ℝ => F q.1 q.2) (Ψ y, 0) ≤ -(2 * ε₀)
            rw [← hγ1]
            simpa using hb
          exact le_trans hΨ (by linarith [hε₀])
        · have hyK : y ∉ Prod.fst '' K := by
            intro hmem
            exact hyA (hK1subA hmem)
          have hfix := houtside_orbit_const y hyA 1 (-1)
          change F ((curveAt Vsusp hcomplete (y, 1) (-1)).1) 0 ≤ 0
          rw [hfix]
          exact (hsign_outside y hyK).2 hy
      · have hval0 : F y 1 ∈ Set.Ioo (-(2 * ε₀)) (2 * ε₀) := by
          constructor
          · exact lt_of_not_ge hdeep
          · exact lt_of_le_of_lt hy (by linarith [hε₀])
        have hyA : y ∈ A := hK1subA ⟨(y, 1), ⟨abs_le.mpr ⟨le_of_lt hval0.1, le_of_lt hval0.2⟩, by norm_num⟩, rfl⟩
        have hconst := hFconstBack y 1 (by norm_num) hval0
        have hγ1 : curveAt Vsusp hcomplete (y, 1) (-1) = (Ψ y, 0) := by
          ext <;> simp [Ψ, hsb1 y hyA]
        have hΨ : F (Ψ y) 0 = F y 1 := by
          change (fun q : M × ℝ => F q.1 q.2) (Ψ y, 0) = F y 1
          rw [← hγ1]
          exact hconst
        rw [hΨ]
        exact hy
  have hbnd_back : ∀ y : M, F y 1 = 0 → F (Ψ y) 0 = 0 := by
    intro y hy
    have hval0 : F y 1 ∈ Set.Ioo (-(2 * ε₀)) (2 * ε₀) := by
      rw [hy]
      constructor <;> linarith [hε₀]
    have hyA : y ∈ A := hK1subA ⟨(y, 1), ⟨abs_le.mpr ⟨le_of_lt hval0.1, le_of_lt hval0.2⟩, by norm_num⟩, rfl⟩
    have hconst := hFconstBack y 1 (by norm_num) hval0
    have hγ1 : curveAt Vsusp hcomplete (y, 1) (-1) = (Ψ y, 0) := by
      ext <;> simp [Ψ, hsb1 y hyA]
    have hΨ : F (Ψ y) 0 = F y 1 := by
      change (fun q : M × ℝ => F q.1 q.2) (Ψ y, 0) = F y 1
      rw [← hγ1]
      exact hconst
    rw [hΨ]
    exact hy
  have hstrict_back : ∀ y : M, F y 1 < 0 → F (Ψ y) 0 < 0 := by
    intro y hy
    by_cases hyD : y ∈ D
    · have hfix := (hDfixprop y hyD).2
      rw [hfix]
      have hle : F y 0 ≤ 0 := (hDsign y hyD).2 (le_of_lt hy)
      have hne : F y 0 ≠ 0 := by
        intro hzero
        have hsep := hDsep y hyD 0 (by norm_num)
        rw [hzero] at hsep
        have hsep' : 2 * ε₀ < 0 := by simpa using hsep
        nlinarith [hε₀, hsep']
      exact lt_of_le_of_ne hle hne
    · by_cases hdeep : F y 1 ≤ -(2 * ε₀)
      · by_cases hyA : y ∈ A
        · have hb : (fun t : ℝ => F (curveAt Vsusp hcomplete (y, 1) (-t)).1 (curveAt Vsusp hcomplete (y, 1) (-t)).2) 1 ≤
              -(2 * ε₀) :=
            sublevel_const_of_deriv_eq_zero_below (hf_back_sm y) (by positivity : (0 : ℝ) < 2 * ε₀)
              (by simpa [curveAt_zero Vsusp hcomplete (y, 1)] using hdeep) (hf_back_deriv0 y)
              (t₁ := (1 : ℝ)) (by norm_num)
          have hγ1 : curveAt Vsusp hcomplete (y, 1) (-1) = (Ψ y, 0) := by
            ext <;> simp [Ψ, hsb1 y hyA]
          have hΨ : F (Ψ y) 0 ≤ -(2 * ε₀) := by
            change (fun q : M × ℝ => F q.1 q.2) (Ψ y, 0) ≤ -(2 * ε₀)
            rw [← hγ1]
            simpa using hb
          exact lt_of_le_of_lt hΨ (by linarith [hε₀])
        · have hyK : y ∉ Prod.fst '' K := by
            intro hmem
            exact hyA (hK1subA hmem)
          have hfix := houtside_orbit_const y hyA 1 (-1)
          change F ((curveAt Vsusp hcomplete (y, 1) (-1)).1) 0 < 0
          rw [hfix]
          have hle : F y 0 ≤ 0 := (hsign_outside y hyK).2 (le_of_lt hy)
          have hne : F y 0 ≠ 0 := by
            intro hzero
            have habs := houtside_strip_abs y hyK 0 (by norm_num)
            rw [hzero] at habs
            have habs' : 2 * ε₀ < 0 := by simpa using habs
            nlinarith [hε₀, habs']
          exact lt_of_le_of_ne hle hne
      · have hval0 : F y 1 ∈ Set.Ioo (-(2 * ε₀)) (2 * ε₀) := by
          constructor
          · exact lt_of_not_ge hdeep
          · exact lt_trans hy (by linarith [hε₀])
        have hyA : y ∈ A := hK1subA ⟨(y, 1), ⟨abs_le.mpr ⟨le_of_lt hval0.1, le_of_lt hval0.2⟩, by norm_num⟩, rfl⟩
        have hconst := hFconstBack y 1 (by norm_num) hval0
        have hγ1 : curveAt Vsusp hcomplete (y, 1) (-1) = (Ψ y, 0) := by
          ext <;> simp [Ψ, hsb1 y hyA]
        have hΨ : F (Ψ y) 0 = F y 1 := by
          change (fun q : M × ℝ => F q.1 q.2) (Ψ y, 0) = F y 1
          rw [← hγ1]
          exact hconst
        rw [hΨ]
        exact hy
  have hinv_back : ∀ y : M, F y 1 ≤ 0 → Φ (Ψ y) = y := by
    intro y hy
    by_cases hyA : y ∈ A
    · have hγ1 : curveAt Vsusp hcomplete (y, 1) (-1) = (Ψ y, 0) := by
        ext <;> simp [Ψ, hsb1 y hyA]
      have hγ0 : curveAt Vsusp hcomplete (y, 1) 0 = (y, 1) := curveAt_zero Vsusp hcomplete (y, 1)
      have hgrp : curveAt Vsusp hcomplete (curveAt Vsusp hcomplete (y, 1) (-1)) 1 = curveAt Vsusp hcomplete (y, 1) 0 := by
        rw [← curveAt_add Vsusp (hVsuspsec.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)) hcomplete (y, 1) (-1) 1]
        norm_num
      rw [hγ1] at hgrp
      rw [hγ0] at hgrp
      dsimp [Φ]
      simpa using congrArg Prod.fst hgrp
    · have hfx : Φ y = y := houtside_orbit_const y hyA 0 1
      have hfy : Ψ y = y := houtside_orbit_const y hyA 1 (-1)
      rw [hfy, hfx]
  refine ⟨Φ, Ψ, hΦsm, hΨsm, hDfixprop, hsub_fwd, hsub_back, hbnd_fwd, hbnd_back,
    hstrict_fwd, hstrict_back, hinv_fwd, hinv_back⟩


theorem regularFamilySliceSmooth
    (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
    (F : M → ℝ → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2)) (s : ℝ) :
    ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun x : M => F x s) := by
  exact hF.comp (contMDiff_id.prodMk contMDiff_const)

theorem regularFamilySliceRegular
    (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
    (F : M → ℝ → ℝ) (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hreg : ∀ q : M × ℝ, |F q.1 q.2| ≤ 2 * ε₀ → q.2 ∈ Set.Icc 0 1 →
      ¬ IsCriticalPointAt I (fun x : M => F x q.2) q.1)
    (s : ℝ) (hs : s = 0 ∨ s = 1) :
    ∀ x : M, F x s = 0 → ¬ IsCriticalPointAt I (fun x : M => F x s) x := by
  intro x hx
  exact hreg (x, s) (by
    simpa [hx] using (mul_nonneg (by norm_num) (le_of_lt hε₀) : (0 : ℝ) ≤ 2 * ε₀)) (by
      rcases hs with rfl | rfl <;> norm_num)

theorem exists_diffeomorph_sublevel_of_regularFamily
    (I : ModelWithCorners ℝ (MorseModel (m + 1)) H) [I.Boundaryless]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M] [SigmaCompactSpace M]
    [FiniteDimensional ℝ (MorseModel (m + 1))] [CompleteSpace (MorseModel (m + 1))]
    (F : M → ℝ → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : M × ℝ => F q.1 q.2))
    (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hstrip : IsCompact {q : M × ℝ | |F q.1 q.2| ≤ 2 * ε₀ ∧ q.2 ∈ Set.Icc 0 1})
    (hreg : ∀ q : M × ℝ, |F q.1 q.2| ≤ 2 * ε₀ → q.2 ∈ Set.Icc 0 1 →
      ¬ IsCriticalPointAt I (fun x : M => F x q.2) q.1)
    (D : Set M) (hDcl : IsClosed D)
    (hDsep : ∀ x : M, x ∈ D → ∀ s : ℝ, s ∈ Set.Icc 0 1 → 2 * ε₀ < |F x s|)
    (hDsign : ∀ x : M, x ∈ D → (F x 0 ≤ 0 ↔ F x 1 ≤ 0))
    (hf₀ : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun x : M => F x 0) :=
      regularFamilySliceSmooth I F hF 0)
    (hreg₀ : ∀ x : M, F x 0 = 0 → ¬ IsCriticalPointAt I (fun x : M => F x 0) x :=
      regularFamilySliceRegular I F ε₀ hε₀ hreg 0 (Or.inl rfl))
    (hf₁ : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun x : M => F x 1) :=
      regularFamilySliceSmooth I F hF 1)
    (hreg₁ : ∀ x : M, F x 1 = 0 → ¬ IsCriticalPointAt I (fun x : M => F x 1) x :=
      regularFamilySliceRegular I F ε₀ hε₀ hreg 1 (Or.inr rfl))
    (hcs₁ : ChartedSpace (MorseHalfSpace m) (SublevelSpace (fun x : M => F x 0) 0) :=
      manifoldSublevelChartedSpace I (fun x : M => F x 0) 0 hf₀ hreg₀)
    (hcs₂ : ChartedSpace (MorseHalfSpace m) (SublevelSpace (fun x : M => F x 1) 0) :=
      manifoldSublevelChartedSpace I (fun x : M => F x 1) 0 hf₁ hreg₁)
    (hchart₁ : ∀ y : SublevelSpace (fun x : M => F x 0) 0, hcs₁.chartAt y =
      (if h : (fun x : M => F x 0) y.1 = 0 then manifoldSublevelBoundaryChart I
          (fun x : M => F x 0) 0 y h hf₀ hreg₀
        else manifoldSublevelInteriorChart I (fun x : M => F x 0) 0 y
          (lt_of_le_of_ne (show (fun x : M => F x 0) y.1 ≤ 0 from y.2) h) hf₀) := by
      intro y
      rfl)
    (hchart₂ : ∀ y : SublevelSpace (fun x : M => F x 1) 0, hcs₂.chartAt y =
      (if h : (fun x : M => F x 1) y.1 = 0 then manifoldSublevelBoundaryChart I
          (fun x : M => F x 1) 0 y h hf₁ hreg₁
        else manifoldSublevelInteriorChart I (fun x : M => F x 1) 0 y
          (lt_of_le_of_ne (show (fun x : M => F x 1) y.1 ≤ 0 from y.2) h) hf₁) := by
      intro y
      rfl) :
    Nonempty (@Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace (fun x : M => F x 0) 0) _ hcs₁
      (SublevelSpace (fun x : M => F x 1) 0) _ hcs₂ (⊤ : ℕ∞)) := by
  classical
  letI := hcs₁
  letI := hcs₂
  rcases exists_relDiffeomorph_sublevel_of_regularFamily (I := I) F hF ε₀ hε₀ hstrip hreg D hDcl
    hDsep hDsign with
    ⟨Φ, Ψ, hΦsm, hΨsm, hDfix, hsub_fwd, hsub_back, hbnd_fwd, hbnd_back,
      hstrict_fwd, hstrict_back, hinv_fwd, hinv_back⟩
  let toFun : SublevelSpace (fun x : M => F x 0) 0 → SublevelSpace (fun x : M => F x 1) 0 :=
    fun x => ⟨Φ x.1, hsub_fwd x.1 x.2⟩
  let invFun : SublevelSpace (fun x : M => F x 1) 0 → SublevelSpace (fun x : M => F x 0) 0 :=
    fun y => ⟨Ψ y.1, hsub_back y.1 y.2⟩
  let e : SublevelSpace (fun x : M => F x 0) 0 ≃ SublevelSpace (fun x : M => F x 1) 0 := by
    refine { toFun := toFun, invFun := invFun, left_inv := ?_, right_inv := ?_ }
    · intro x
      apply Subtype.ext
      exact hinv_fwd x.1 x.2
    · intro y
      apply Subtype.ext
      exact hinv_back y.1 y.2
  let d : @Diffeomorph ℝ _ (MorseModel (m + 1)) _ _ (MorseModel (m + 1)) _ _
      (MorseHalfSpace m) _ (MorseHalfSpace m) _ (morseModelWithCornersHalfSpace m)
      (morseModelWithCornersHalfSpace m)
      (SublevelSpace (fun x : M => F x 0) 0) _ hcs₁
      (SublevelSpace (fun x : M => F x 1) 0) _ hcs₂ (⊤ : ℕ∞) := by
    refine { toEquiv := e, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
    · simpa [toFun] using contMDiff_manifoldSublevelMap (I := I)
        (fun x : M => F x 0) (fun x : M => F x 1) 0 0 hf₀ hf₁ hreg₀ hreg₁
        Φ hΦsm hsub_fwd hbnd_fwd hstrict_fwd
        (hcs₁ := hcs₁) (hcs₂ := hcs₂) (hchart₁ := hchart₁) (hchart₂ := hchart₂)
    · simpa [invFun] using contMDiff_manifoldSublevelMap (I := I)
        (fun x : M => F x 1) (fun x : M => F x 0) 0 0 hf₁ hf₀ hreg₁ hreg₀
        Ψ hΨsm hsub_back hbnd_back hstrict_back
        (hcs₁ := hcs₂) (hcs₂ := hcs₁) (hchart₁ := hchart₂) (hchart₂ := hchart₁)
  exact ⟨d⟩
end
end DifferentialGeometry.Topology.Morse
