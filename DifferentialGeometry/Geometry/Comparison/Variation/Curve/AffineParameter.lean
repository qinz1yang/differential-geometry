import DifferentialGeometry.Geometry.Comparison.Variation.Field.Smoothness

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open Bundle Filter Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem mfderiv_affine_parameter
    {alpha : E × ℝ → M} (A B : E) (s : ℝ)
    (halpha : ContMDiffAt
      (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I ∞ alpha (A, s)) :
    mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ alpha (A + u • B, s)) 0 (1 : ℝ) =
      mfderiv 𝓘(ℝ, E) I (fun W : E ↦ alpha (W, s)) A B := by
  let line : ℝ → E := fun u ↦ A + u • B
  let phi : E → M := fun W ↦ alpha (W, s)
  have hfoot : line 0 = A := by
    simp only [line, zero_smul, add_zero]
  have hincl : ContMDiffAt 𝓘(ℝ, E)
      (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞
      (fun W : E ↦ (W, s)) A :=
    (contMDiff_id.prodMk contMDiff_const).contMDiffAt
  have hslice : ContMDiffAt 𝓘(ℝ, E) I ∞ phi A := by
    have hcomp := halpha.comp A hincl
    have hfun : alpha ∘ (fun W : E ↦ (W, s)) = phi := by rfl
    rw [hfun] at hcomp
    exact hcomp
  have hphi : MDifferentiableAt 𝓘(ℝ, E) I phi A :=
    hslice.mdifferentiableAt (by simp)
  have hphi' : MDifferentiableAt 𝓘(ℝ, E) I phi (line 0) := by
    rw [hfoot]
    exact hphi
  have hline : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) line 0 := by
    have hlineCD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ line := by
      have hraw := (contMDiff_const.add
        (contMDiff_id.smul contMDiff_const) :
          ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
            ((fun _ : ℝ ↦ A) + fun u : ℝ ↦ u • B))
      have hfun : ((fun _ : ℝ ↦ A) + fun u : ℝ ↦ u • B) = line := by
        funext u
        rfl
      rw [hfun] at hraw
      exact hraw
    exact hlineCD.contMDiffAt.mdifferentiableAt (by simp)
  have hline_apply :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) line 0 (1 : ℝ) = B := by
    rw [mfderiv_eq_fderiv]
    have hfd : HasFDerivAt line
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) B) 0 := by
      have hraw : HasFDerivAt (fun x : ℝ ↦ A + id x • B)
          (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) B) 0 :=
        ((hasFDerivAt_id (0 : ℝ)).smul_const B).const_add A
      have hfun : (fun x : ℝ ↦ A + id x • B) = line := by
        funext u
        rfl
      rw [hfun] at hraw
      exact hraw
    rw [hfd.fderiv]
    change (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) B)
      (1 : ℝ) = B
    rw [ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self, one_smul]
  have hcomp := mfderiv_comp_apply (f := line) (g := phi) (x := (0 : ℝ))
    hphi' hline (1 : ℝ)
  change mfderiv 𝓘(ℝ, ℝ) I (phi ∘ line) 0 (1 : ℝ) =
    mfderiv 𝓘(ℝ, E) I phi A B
  rw [hcomp, hline_apply, hfoot]

variable [IsManifold I ∞ M]

theorem contMDiffOn_affine_variationField
    {alpha : E × ℝ → M} {V : Set E} {K : Set ℝ} {A0 B : E}
    (hVopen : IsOpen V) (hA0V : A0 ∈ V) (hKopen : IsOpen K)
    (halpha : ContMDiffOn
      (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I ∞ alpha (V ×ˢ K)) :
    ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun s : ℝ ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha (A0, s))
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun u : ℝ ↦ alpha (A0 + u • B, s)) 0 (1 : ℝ)) :
          TangentBundle I M)) K := by
  let f : ℝ → ℝ → M := fun u s ↦ alpha (A0 + u • B, s)
  have hf : ∀ s ∈ K, ContMDiffAt
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun p : ℝ × ℝ ↦ f p.1 p.2) (0, s) := by
    intro s hs
    have hparam : ContMDiffAt
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞
        (fun p : ℝ × ℝ ↦ (A0 + p.1 • B, p.2)) (0, s) :=
      ((contMDiff_const.add
        (contMDiff_fst.smul contMDiff_const)).prodMk
          contMDiff_snd).contMDiffAt
    have halphaAt : ContMDiffAt
        (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I ∞ alpha (A0, s) :=
      (halpha (A0, s) ⟨hA0V, hs⟩).contMDiffAt
        ((hVopen.prod hKopen).mem_nhds ⟨hA0V, hs⟩)
    have hcomp := halphaAt.comp_of_eq hparam (by
      simp only [zero_smul, add_zero])
    rw [show (alpha ∘ fun p : ℝ × ℝ ↦ (A0 + p.1 • B, p.2)) =
      (fun p : ℝ × ℝ ↦ alpha (A0 + p.1 • B, p.2)) by rfl] at hcomp
    exact hcomp
  have hsmooth := varField_smoothOn (I := I) f hf
  have heq : (fun s : ℝ ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha (A0, s))
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun u : ℝ ↦ alpha (A0 + u • B, s)) 0 (1 : ℝ)) :
          TangentBundle I M)) =
      (fun s : ℝ ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (f 0 s)
          (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ f u s) 0 (1 : ℝ)) :
          TangentBundle I M)) := by
    funext s
    dsimp only [f]
    rw [zero_smul, add_zero]
    rfl
  rw [heq]
  exact hsmooth

variable [FiniteDimensional ℝ E]

theorem covDerivAlong_affine_variationField_at_fixed_start
    (g : SmoothRiemannianMetric I M)
    {alpha : E × ℝ → M} {V : Set E} {A0 B : E} {s0 : ℝ} (x : M)
    (hVopen : IsOpen V) (hA0V : A0 ∈ V)
    (halpha : ContMDiffAt
      (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I ∞ alpha (A0, s0))
    (hfixed : ∀ A ∈ V, alpha (A, s0) = x)
    (hlaunch : ∀ A ∈ V,
      mfderiv 𝓘(ℝ, ℝ) I (fun r ↦ alpha (A, r)) s0 (1 : ℝ) = A) :
    covDerivAlong (I := I) g (fun r ↦ alpha (A0, r))
        (fun r ↦ mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ ↦ alpha (A0 + u • B, r)) 0 (1 : ℝ)) s0 = B := by
  let line : ℝ → E := fun u ↦ A0 + u • B
  let F : ℝ → ℝ → M := fun u r ↦ alpha (line u, r)
  have hline : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ line := by
    have hraw := (contMDiff_const.add
      (contMDiff_id.smul contMDiff_const) :
        ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
          ((fun _ : ℝ ↦ A0) + fun u : ℝ ↦ u • B))
    have hfun : ((fun _ : ℝ ↦ A0) + fun u : ℝ ↦ u • B) = line := by
      funext u
      rfl
    rw [hfun] at hraw
    exact hraw
  have hline0 : line 0 = A0 := by
    simp only [line, zero_smul, add_zero]
  have hline0V : line 0 ∈ V := by
    rw [hline0]
    exact hA0V
  have hnear : ∀ᶠ u in nhds (0 : ℝ), line u ∈ V := by
    have hpre := hline.continuous.continuousAt.preimage_mem_nhds
      (hVopen.mem_nhds hline0V)
    exact hpre
  have hparam : ContMDiffAt
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : ℝ × ℝ ↦ (line q.1, q.2)) (0, s0) := by
    exact ((contMDiff_const.add
      (contMDiff_fst.smul contMDiff_const)).prodMk
        contMDiff_snd).contMDiffAt
  have halphaAt : ContMDiffAt
      (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I ∞ alpha (line 0, s0) := by
    simpa only [hline0] using halpha
  have hFInf : ContMDiffAt
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun q : ℝ × ℝ ↦ F q.1 q.2) (0, s0) := by
    have hcomp := halphaAt.comp (0, s0) hparam
    have hfun : alpha ∘ (fun q : ℝ × ℝ ↦ (line q.1, q.2)) =
        (fun q : ℝ × ℝ ↦ F q.1 q.2) := by rfl
    rw [hfun] at hcomp
    exact hcomp
  have hF2 : ContMDiffAt
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I 2
      (fun q : ℝ × ℝ ↦ F q.1 q.2) (0, s0) :=
    hFInf.of_le (by
      change (↑(2 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
      exact WithTop.coe_le_coe.mpr le_top)
  have hfev : ∀ᶠ q in nhds ((0 : ℝ), s0),
      ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I 2
        (fun p : ℝ × ℝ ↦ F p.1 p.2) q :=
    (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hF2
  have hlineU : Tendsto (fun u : ℝ ↦ (u, s0)) (nhds 0) (nhds (0, s0)) :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hlineR : Tendsto (fun r : ℝ ↦ ((0 : ℝ), r))
      (nhds s0) (nhds (0, s0)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hslice_u : ∀ᶠ u in nhds (0 : ℝ),
      ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun r : ℝ ↦ F u r) s0 := by
    filter_upwards [hlineU.eventually hfev] with u hu
    have hincl : ContMDiffAt 𝓘(ℝ, ℝ)
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 2
        (fun r : ℝ ↦ (u, r)) s0 :=
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    exact hu.comp s0 hincl
  have hslice_v : ∀ᶠ r in nhds s0,
      ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun u : ℝ ↦ F u r) 0 := by
    filter_upwards [hlineR.eventually hfev] with r hr
    have hincl : ContMDiffAt 𝓘(ℝ, ℝ)
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 2
        (fun u : ℝ ↦ (u, r)) 0 :=
      (contMDiff_id.prodMk contMDiff_const).contMDiffAt
    have hcomp : ContMDiffAt 𝓘(ℝ, ℝ) I 2
        ((fun p : ℝ × ℝ ↦ F p.1 p.2) ∘
          fun u : ℝ ↦ (u, r)) 0 :=
      hr.comp 0 hincl
    have hfun : ((fun p : ℝ × ℝ ↦ F p.1 p.2) ∘
        fun u : ℝ ↦ (u, r)) = (fun u : ℝ ↦ F u r) := by rfl
    rw [hfun] at hcomp
    exact hcomp
  have htrans : ContinuousAt (fun u : ℝ ↦ F u s0) 0 := by
    have hincl : ContMDiffAt 𝓘(ℝ, ℝ)
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 2
        (fun u : ℝ ↦ (u, s0)) 0 :=
      (contMDiff_id.prodMk contMDiff_const).contMDiffAt
    exact (hF2.comp 0 hincl).continuousAt
  have hcentral : ContinuousAt (fun r : ℝ ↦ F 0 r) s0 := by
    have hincl : ContMDiffAt 𝓘(ℝ, ℝ)
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 2
        (fun r : ℝ ↦ ((0 : ℝ), r)) s0 :=
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    exact (hF2.comp s0 hincl).continuousAt
  have hsrc : F 0 s0 ∈ (chartAt H (F 0 s0)).source :=
    mem_chart_source H (F 0 s0)
  have hext : ContMDiffAt I 𝓘(ℝ, E) 2
      (extChartAt I (F 0 s0)) (F 0 s0) :=
    contMDiffAt_extChartAt' (I := I) (n := 2) (x := F 0 s0) hsrc
  have hpull : ContMDiffAt
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) 2
      (fun q : ℝ × ℝ ↦ extChartAt I (F 0 s0) (F q.1 q.2))
      (0, s0) := by
    exact hext.comp (0, s0) hF2
  have hcoord : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ ↦ extChartAt I (F 0 s0) (F q.1 q.2))
      (0, s0) := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hpull
  have hcomm :=
    covDerivAlong_commute_transverse_longitudinal_of_variation
      (I := I) g F s0 hcoord hslice_u hslice_v htrans hcentral
  have hfixedEv : (fun u : ℝ ↦ F u s0) =ᶠ[nhds 0]
      (fun _ ↦ x) := by
    filter_upwards [hnear] with u hu
    exact hfixed (line u) hu
  have hlaunchEv :
      (fun u : ℝ ↦ mfderiv 𝓘(ℝ, ℝ) I (F u) s0 (1 : ℝ)) =ᶠ[nhds 0]
        line := by
    filter_upwards [hnear] with u hu
    exact hlaunch (line u) hu
  have hlineDeriv : HasDerivAt line B 0 := by
    simpa only [line, id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const B).const_add A0
  have hLHS := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
    (I := I) g (fun u ↦ mfderiv 𝓘(ℝ, ℝ) I (F u) s0 (1 : ℝ)) line
      hfixedEv hlaunchEv
  have hconst := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_const
    (I := I) g x line 0 hlineDeriv.differentiableAt
  have hleft : covDerivAlong (I := I) g (fun u : ℝ ↦ F u s0)
      (fun u ↦ mfderiv 𝓘(ℝ, ℝ) I (F u) s0 (1 : ℝ)) 0 = B :=
    hLHS.trans (hconst.trans hlineDeriv.deriv)
  have hright := hcomm.symm.trans hleft
  have hcurve : (fun r : ℝ ↦ alpha (A0, r)) = F 0 := by
    funext r
    simp only [F, line, zero_smul, add_zero]
  rw [hcurve]
  exact hright

end DifferentialGeometry.Geometry.Riemannian.Variation
