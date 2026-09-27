import DifferentialGeometry.Geometry.Connection.ParallelTransport.Construction.Smoothness
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import Mathlib.Algebra.Order.Field.Pi
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Curve

open Set Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

open CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

private theorem exists_parallel_frame_of_contMDiff
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    {N : ℕ} (hN : 2 ≤ N) (hγ : ContMDiff 𝓘(ℝ, ℝ) I (N : ℕ∞) γ) {L : ℝ} (hL : 0 < L)
    {ι : Type*} [DecidableEq ι] (v : ι → TangentSpace I (γ 0))
    (hON0 : ∀ i j, g.inner (γ 0) (v i) (v j) = if i = j then (1 : ℝ) else 0) :
    ∃ e : ι → ∀ t : ℝ, TangentSpace I (γ t),
      (∀ i, e i 0 = v i) ∧
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        DifferentiableAt ℝ (chartRepAt (I := I) γ (e i) t) t) ∧
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        covDerivAlong (I := I) g γ (e i) t = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i j,
        g.inner (γ t) (e i t) (e j t) = if i = j then 1 else 0) := by
  classical
  have htransport : ∀ i, ∃ V : ∀ t, TangentSpace I (γ t),
      V 0 = v i ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, DifferentiableAt ℝ (chartRepAt (I := I) γ V t) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, covDerivAlong (I := I) g γ V t = 0) :=
    fun i =>
      Variation.exists_parallel_transport_on_Icc
        (I := I) g γ hN hγ hL (v i)
  choose Vfun hV0 hVdiff hVpar using htransport
  refine ⟨Vfun, hV0, hVdiff, hVpar, ?_⟩
  intro t ht i j
  have hconst :=
    Variation.parallel_transport_preserves_inner_product
      (I := I) g γ hN hγ (Vfun i) (Vfun j)
      (hVdiff i) (hVdiff j) (hVpar i) (hVpar j) t ht
  rw [hconst, hV0 i, hV0 j]
  exact hON0 i j

private theorem exists_parallel_frame_on_Icc_zero
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) {U : Set ℝ} {L : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ U)
    (hU : IsOpen U) (hL : 0 ≤ L) (hseg : Icc (0 : ℝ) L ⊆ U)
    {ι : Type*} [DecidableEq ι] (v : ι → TangentSpace I (γ 0))
    (hON0 : ∀ i j, g.inner (γ 0) (v i) (v j) = if i = j then (1 : ℝ) else 0) :
    ∃ F : ι → ∀ t : ℝ, TangentSpace I (γ t),
      (∀ i, F i 0 = v i) ∧
      (∀ i, ∀ t ∈ Icc (0 : ℝ) L,
        DifferentiableAt ℝ (chartRepAt (I := I) γ (F i) t) t) ∧
      (∀ i, ∀ t ∈ Icc (0 : ℝ) L, covDerivAlong (I := I) g γ (F i) t = 0) ∧
      (∀ t ∈ Icc (0 : ℝ) L, ∀ i j,
        g.inner (γ t) (F i t) (F j t) = if i = j then (1 : ℝ) else 0) := by
  obtain ⟨Γ, hΓ, hgerm⟩ := hγ.exists_extension_uIcc (a := 0) (b := L) hU
    (by simpa only [uIcc_of_le hL] using hseg)
  rw [uIcc_of_le hL] at hgerm
  let w : ι → TangentSpace I (Γ 0) := fun i => show TangentSpace I (Γ 0) from (v i : E)
  have hbase : Γ 0 = γ 0 := (hgerm 0 ⟨le_rfl, hL⟩).eq_of_nhds
  have hONw : ∀ i j, g.inner (Γ 0) (w i) (w j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    change g.inner (Γ 0) (show TangentSpace I (Γ 0) from (v i : E))
      (show TangentSpace I (Γ 0) from (v j : E)) = _
    rw [hbase]
    exact hON0 i j
  obtain ⟨FG, hFG0, hFGdiff, hFGpar, hFGON⟩ :=
    exists_parallel_frame_of_contMDiff (I := I) g Γ (N := 2) (by norm_num) hΓ
      (lt_of_lt_of_le zero_lt_one (le_max_right L 1)) w hONw
  let F : ι → ∀ t : ℝ, TangentSpace I (γ t) :=
    fun i t => show TangentSpace I (γ t) from (FG i t : E)
  have hfield : ∀ i t,
      (fun s : ℝ => (F i s : E)) =ᶠ[𝓝 t] fun s : ℝ => (FG i s : E) :=
    fun _ _ => Filter.Eventually.of_forall fun _ => rfl
  have hsub : Icc (0 : ℝ) L ⊆ Icc (0 : ℝ) (max L 1) :=
    Icc_subset_Icc_right (le_max_left L 1)
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hFG0 i
  · intro i t ht
    have hrep := chartRep_congr_curve (I := I) (F i) (FG i)
      (hgerm t ht).symm (hfield i t)
    exact hrep.differentiableAt_iff.mpr (hFGdiff i t (hsub ht))
  · intro i t ht
    have hcongr := covDerivAlong_congr_curve (I := I) g (F i) (FG i)
      (hgerm t ht).symm (hfield i t)
    exact hcongr.trans (hFGpar i t (hsub ht))
  · intro t ht i j
    have hpoint : Γ t = γ t := (hgerm t ht).eq_of_nhds
    change g.inner (γ t) (show TangentSpace I (γ t) from (FG i t : E))
      (show TangentSpace I (γ t) from (FG j t : E)) = _
    rw [← hpoint]
    exact hFGON t (hsub ht) i j

theorem exists_parallel_frame_on_Icc
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) {U : Set ℝ} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ U)
    (hU : IsOpen U) (hab : a ≤ b) (hseg : Icc a b ⊆ U)
    {ι : Type*} [DecidableEq ι] (v : ι → TangentSpace I (γ a))
    (hON0 : ∀ i j, g.inner (γ a) (v i) (v j) = if i = j then (1 : ℝ) else 0) :
    ∃ F : ι → ∀ t : ℝ, TangentSpace I (γ t),
      (∀ i, F i a = v i) ∧
      (∀ i, ∀ t ∈ Icc a b,
        DifferentiableAt ℝ (chartRepAt (I := I) γ (F i) t) t) ∧
      (∀ i, ∀ t ∈ Icc a b, covDerivAlong (I := I) g γ (F i) t = 0) ∧
      (∀ t ∈ Icc a b, ∀ i j,
        g.inner (γ t) (F i t) (F j t) = if i = j then (1 : ℝ) else 0) := by
  let Γ : ℝ → M := fun s => γ (s + a)
  let V : Set ℝ := (fun s : ℝ => s + a) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_id.add continuous_const)
  have hΓ : ContMDiffOn 𝓘(ℝ, ℝ) I (2 : ℕ∞) Γ V :=
    hγ.comp ((contDiff_id.add contDiff_const).contMDiff.contMDiffOn) (fun _ h => h)
  have hVseg : Icc (0 : ℝ) (b - a) ⊆ V := by
    intro t ht
    exact hseg ⟨by linarith [ht.1], by linarith [ht.2]⟩
  let w : ι → TangentSpace I (Γ 0) := fun i => show E from v i
  have hONw : ∀ i j, g.inner (Γ 0) (w i) (w j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    change g.inner (γ (0 + a)) (show TangentSpace I (γ (0 + a)) from (v i : E))
      (show TangentSpace I (γ (0 + a)) from (v j : E)) = _
    rw [zero_add]
    exact hON0 i j
  obtain ⟨FΓ, hFΓ0, hFΓdiff, hFΓpar, hFΓON⟩ :=
    exists_parallel_frame_on_Icc_zero
      g Γ hΓ hV (sub_nonneg.mpr hab) hVseg w hONw
  let F : ι → ∀ t : ℝ, TangentSpace I (γ t) := fun i t => show E from FΓ i (t - a)
  have htshift t (ht : t ∈ Icc a b) : t - a ∈ Icc (0 : ℝ) (b - a) :=
    ⟨sub_nonneg.mpr ht.1, sub_le_sub_right ht.2 a⟩
  have hcurve t : γ =ᶠ[𝓝 t] (fun s => Γ (s - a)) :=
    Eventually.of_forall fun s => by simp only [Γ, sub_add_cancel]
  have hfield i t : ∀ᶠ s in 𝓝 t, (F i s : E) = (FΓ i (s - a) : E) :=
    Eventually.of_forall fun _ => rfl
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro i
    change (FΓ i (a - a) : E) = (v i : E)
    rw [sub_self]
    exact hFΓ0 i
  · intro i t ht
    have hcomp := (hFΓdiff i (t - a) (htshift t ht)).comp t
      (differentiableAt_id.sub_const a)
    have hrep := chartRep_congr_curve (I := I) (F i) (fun s => FΓ i (s - a))
      (hcurve t) (hfield i t)
    apply hrep.differentiableAt_iff.mpr
    exact hcomp
  · intro i t ht
    have htV : t - a ∈ V := hVseg (htshift t ht)
    have hΓat : MDifferentiableAt 𝓘(ℝ, ℝ) I Γ (t - a) :=
      ((hΓ (t - a) htV).contMDiffAt (hV.mem_nhds htV)).mdifferentiableAt (by norm_num)
    have hcomp := covDerivAlong_comp g Γ (FΓ i) (fun s => s - a) t hΓat
      (hFΓdiff i (t - a) (htshift t ht)) (differentiableAt_id.sub_const a)
    rw [hFΓpar i (t - a) (htshift t ht), smul_zero] at hcomp
    exact (covDerivAlong_congr_curve g (F i) (fun s => FΓ i (s - a))
      (hcurve t) (hfield i t)).trans hcomp
  · intro t ht i j
    have h := hFΓON (t - a) (htshift t ht) i j
    change g.inner (γ (t - a + a))
      (show TangentSpace I (γ (t - a + a)) from (FΓ i (t - a) : E))
      (show TangentSpace I (γ (t - a + a)) from (FΓ j (t - a) : E)) = _ at h
    rw [sub_add_cancel] at h
    exact h

theorem exists_parallel_frame
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    {N : ℕ} (hN : 2 ≤ N) (hγ : ContMDiff 𝓘(ℝ, ℝ) I (N : ℕ∞) γ) {L : ℝ} (hL : 0 < L)
    {ι : Type*} [DecidableEq ι] (v : ι → TangentSpace I (γ 0))
    (hON0 : ∀ i j, g.inner (γ 0) (v i) (v j) = if i = j then (1 : ℝ) else 0) :
    ∃ e : ι → ∀ t : ℝ, TangentSpace I (γ t),
      (∀ i, e i 0 = v i) ∧
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        DifferentiableAt ℝ (chartRepAt (I := I) γ (e i) t) t) ∧
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) L,
        covDerivAlong (I := I) g γ (e i) t = 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) L, ∀ i j,
        g.inner (γ t) (e i t) (e j t) = if i = j then 1 else 0) := by
  exact exists_parallel_frame_on_Icc (I := I) (a := 0) (b := L) g γ
    (hγ.of_le (by exact_mod_cast hN)).contMDiffOn isOpen_univ hL.le
    (subset_univ _) v hON0

open Variation Bundle in
theorem exists_smooth_parallel_frame_on_Ioo
    (q : SmoothRiemannianMetric I M) (alpha : Real → M)
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I ∞ alpha)
    {a b : Real} (hab : a ≤ b)
    {ι : Type*} [Finite ι] [DecidableEq ι] (v : ι → TangentSpace I (alpha b))
    (hON : ∀ i j, q.inner (alpha b) (v i) (v j) = if i = j then 1 else 0) :
    ∃ (eps : Real) (_ : 0 < eps)
      (F : ι → ∀ s, TangentSpace I (alpha s)),
      (∀ i, F i b = v i) ∧
      (∀ i, ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
        (fun s : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (alpha s) (F i s) : TangentBundle I M)) (Set.Ioo (a - eps) (b + eps))) ∧
      (∀ i, ∀ s ∈ Set.Ioo (a - eps) (b + eps),
        DifferentiableAt Real (chartRepAt (I := I) alpha (F i) s) s) ∧
      (∀ i, ∀ s ∈ Set.Ioo (a - eps) (b + eps),
        covDerivAlong (I := I) q alpha (F i) s = 0) ∧
      (∀ s ∈ Set.Ioo (a - eps) (b + eps), ∀ i j,
        q.inner (alpha s) (F i s) (F j s) = if i = j then 1 else 0) := by
  classical
  let L := b - a + 1
  have hL : 0 < L := by dsimp only [L]; linarith
  let beta : Real → M := fun r ↦ alpha (b - r)
  have hbeta : ContMDiff (modelWithCornersSelf Real Real) I ∞ beta := by
    exact halpha.comp (contMDiff_const.sub contMDiff_id)
  have htransport : ∀ i, ∃ (d : Real) (_ : 0 < d)
      (P : ∀ r, TangentSpace I (beta r)),
      P 0 = v i ∧
      (∀ r ∈ Set.Ioo (-d) (L + d),
        DifferentiableAt Real (chartRepAt (I := I) beta P r) r) ∧
      (∀ r ∈ Set.Ioo (-d) (L + d),
        covDerivAlong (I := I) q beta P r = 0) ∧
      ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
        (fun r : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (beta r) (P r) : TangentBundle I M)) (Set.Ioo (-d) (L + d)) :=
    fun i ↦ parallelTransport_section_contMDiffOn_Ioo
      (I := I) q beta hbeta hL (v i)
  choose d hd P hP0 hPdiff hPpar hPsmooth using htransport
  obtain ⟨eps, heps, hepsd⟩ :=
    Pi.exists_forall_pos_add_lt (x := fun _ : ι ↦ 0)
      (y := d) (fun i ↦ hd i)
  have heps_lt (i : ι) : eps < d i := by
    simpa only [zero_add] using hepsd i
  let phi : Real → Real := fun s ↦ b - s
  let F : ι → ∀ s, TangentSpace I (alpha s) :=
    fun i s ↦ P i (phi s)
  have hphi : ContMDiff (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞ phi :=
    contMDiff_const.sub contMDiff_id
  have hphiDiff : Differentiable Real phi :=
    (contMDiff_iff_contDiff.mp hphi).differentiable (by simp)
  have hcurve : (fun s ↦ beta (phi s)) = alpha := by
    funext s
    dsimp only [beta, phi]
    congr 1
    ring
  have hrev (s : Real) (hs : s ∈ Set.Ioo (a - eps) (b + eps))
      (i : ι) :
      phi s ∈ Set.Ioo (-(d i)) (L + d i) := by
    dsimp only [phi]
    constructor <;> linarith [hs.1, hs.2, heps_lt i, show L = b - a + 1 from rfl]
  have hFsmooth : ∀ i, ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (F i s) : TangentBundle I M)) (Set.Ioo (a - eps) (b + eps)) := by
    intro i
    have hcomp := (hPsmooth i).comp hphi.contMDiffOn
      (fun s hs ↦ hrev s hs i)
    have heq :
        ((fun r : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (beta r) (P i r) : TangentBundle I M)) ∘ phi) =
          (fun s : Real ↦
            (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
              (alpha s) (F i s) : TangentBundle I M)) := by
      funext s
      simp only [Function.comp_apply, F]
      rw [congrFun hcurve s]
    rwa [heq] at hcomp
  have hFdiff : ∀ i, ∀ s ∈ Set.Ioo (a - eps) (b + eps),
      DifferentiableAt Real (chartRepAt (I := I) alpha (F i) s) s := by
    intro i s hs
    have hAt := (hFsmooth i s hs).contMDiffAt (isOpen_Ioo.mem_nhds hs)
    exact (differentiableAt_chartRepAt_of_contMDiffAt_two (I := I) (hAt.of_le (by
      change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))))
  have hFpar : ∀ i, ∀ s ∈ Set.Ioo (a - eps) (b + eps),
      covDerivAlong (I := I) q alpha (F i) s = 0 := by
    intro i s hs
    have hcomp := covDerivAlong_comp (I := I) q beta (P i) phi s
      (hbeta.mdifferentiableAt (by simp)) (hPdiff i (phi s) (hrev s hs i))
      hphiDiff.differentiableAt
    have hzero := hPpar i (phi s) (hrev s hs i)
    rw [hzero, smul_zero] at hcomp
    rw [hcurve] at hcomp
    exact hcomp
  have hFON : ∀ s ∈ Set.Ioo (a - eps) (b + eps), ∀ i j,
      q.inner (alpha s) (F i s) (F j s) = if i = j then 1 else 0 := by
    intro s hs i j
    let r := phi s
    let lo := min 0 r
    let hi := max 0 r
    have hr_mem : r ∈ Set.Icc lo hi := ⟨min_le_right _ _, le_max_right _ _⟩
    have h0_mem : (0 : Real) ∈ Set.Icc lo hi :=
      ⟨min_le_left _ _, le_max_left _ _⟩
    have hseg : Set.Icc lo hi ⊆ Set.Ioo (-(d i)) (L + d i) := by
      intro z hz
      have hrange := hrev s hs i
      dsimp only [lo, hi] at hz
      rcases le_total 0 r with hr | hr
      · rw [min_eq_left hr, max_eq_right hr] at hz
        constructor <;> linarith [hz.1, hz.2, hrange.1, hrange.2, hd i, hL]
      · rw [min_eq_right hr, max_eq_left hr] at hz
        constructor <;> linarith [hz.1, hz.2, hrange.1, hrange.2, hd i, hL]
    have hsegj : Set.Icc lo hi ⊆ Set.Ioo (-(d j)) (L + d j) := by
      intro z hz
      have hrange := hrev s hs j
      dsimp only [lo, hi] at hz
      rcases le_total 0 r with hr | hr
      · rw [min_eq_left hr, max_eq_right hr] at hz
        constructor <;> linarith [hz.1, hz.2, hrange.1, hrange.2, hd j, hL]
      · rw [min_eq_right hr, max_eq_left hr] at hz
        constructor <;> linarith [hz.1, hz.2, hrange.1, hrange.2, hd j, hL]
    have hconst := parallel_transport_preserves_inner_product (I := I) q beta
      (N := 2) le_rfl (hbeta.of_le (by exact_mod_cast le_top)) (P i) (P j)
      (fun z hz ↦ hPdiff i z (hseg hz))
      (fun z hz ↦ hPdiff j z (hsegj hz))
      (fun z hz ↦ hPpar i z (hseg hz))
      (fun z hz ↦ hPpar j z (hsegj hz))
    have hr_eq := hconst r hr_mem
    have h0_eq := hconst 0 h0_mem
    have hrbase : beta r = alpha s := by
      dsimp only [r, beta, phi]
      congr 1
      ring
    dsimp only [F]
    rw [← hrbase]
    rw [hr_eq, ← h0_eq, hP0 i, hP0 j]
    have hbeta0 : beta 0 = alpha b := by
      dsimp only [beta]
      congr 1
      ring
    rw [hbeta0]
    exact hON i j
  refine ⟨eps, heps, F, ?_, hFsmooth, hFdiff, hFpar, hFON⟩
  intro i
  change P i (b - b) = v i
  rw [sub_self]
  exact hP0 i

theorem exists_smooth_parallel_orthonormal_frame_on_Ioo
    (q : SmoothRiemannianMetric I M) (alpha : Real → M)
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I ∞ alpha)
    {a b : Real} (hab : a ≤ b) :
    ∃ (eps : Real) (_ : 0 < eps)
      (F : Fin (Module.finrank Real E) → ∀ s, TangentSpace I (alpha s)),
      (∀ i, ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
        (fun s : Real ↦
          (Bundle.TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (alpha s) (F i s) : TangentBundle I M)) (Set.Ioo (a - eps) (b + eps))) ∧
      (∀ i, ∀ s ∈ Set.Ioo (a - eps) (b + eps),
        DifferentiableAt Real (chartRepAt (I := I) alpha (F i) s) s) ∧
      (∀ i, ∀ s ∈ Set.Ioo (a - eps) (b + eps),
        covDerivAlong (I := I) q alpha (F i) s = 0) ∧
      (∀ s ∈ Set.Ioo (a - eps) (b + eps), ∀ i j,
        q.inner (alpha s) (F i s) (F j s) = if i = j then 1 else 0) := by
  obtain ⟨basis, hbasis⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) q (alpha b)
  obtain ⟨eps, heps, F, _, hF⟩ :=
    exists_smooth_parallel_frame_on_Ioo q alpha halpha hab basis hbasis
  exact ⟨eps, heps, F, hF⟩

end DifferentialGeometry.Geometry.Riemannian
