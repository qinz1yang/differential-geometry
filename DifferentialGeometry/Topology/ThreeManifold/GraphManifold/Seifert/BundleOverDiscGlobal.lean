import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BundleOverDisc
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.RegularSublevelAtlas
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Maps
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Orientation
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Circle bundles over a disc: the global case and restriction to sub-surfaces

Chapter 6, lane RG01b, continuing `Seifert/BundleOverDisc.lean` (RG01a).

(B) `discCircleCocycleTrivial` proves `DiscCircleCocycleTrivial`: on a compact surface `B`
diffeomorphic to a `PlanarBase 1`, every finite smooth `Circle`-valued Čech cocycle is a smooth
coboundary on the same cover. `CircleCocycleTrivialOn I V g S` says the cocycle is a smooth
coboundary over `S`. It holds over any set inside one `V m`, and over `S ∪ T` for open `S`, `T`
when it holds over both, every smooth circle-valued map on `S ∩ T` has a smooth real lift
(`Circle.exp`), and a smooth `ρ` is `0` near `S \ T` and `1` near `T \ S`
(`CircleCocycleTrivialOn.union`: correct by `exp (ρ f)` and `exp ((ρ - 1) f)` for a lift `f` of
the discrepancy). Lifts exist over preimages of convex open sets under a smooth embedding
`ε : B → ℂ` with convex range: such a preimage is contractible, a continuous logarithm exists
(`Complex.exists_continuousOn_eqOn_exp_comp`), and a continuous lift of a smooth map is smooth
(`contMDiffOn_of_circleExp_eq`, by the branch `arg` near each point). Sweeping a linear
coordinate across slabs (`CircleCocycleTrivialOn.sweep`), first across small rectangles inside a
Lebesgue ball of the cover, then across horizontal strips, gives the coboundary on all of `B`
(`circleCocycleTrivialOn_univ`); `ε` is the planar embedding of the `PlanarBase 1`. Hence a
circle fibration over a disc with a principal atlas is a product
(`PrincipalAtlas.isGloballyTrivial_of_planarBase`), and `CircleBundlesOverDiscStandard` is
equivalent to the existence of principal atlases unconditionally
(`circleBundlesOverDiscStandard_iff_nonempty_principalAtlas`).

(A) Restriction. For a circle fibration `F` and a closed connected subset `K` of its base with a
`SmoothBoundaryAtlas` `A` (a compact sub-surface with boundary in the interior of the base, for
instance a closed sub-disc), `CircleFibration.restrict F A hK` is a circle fibration of the
compact carrier `restrictTotal F A hK` (the subtype `π⁻¹ K` of `U`, with the boundary atlas
`totalAtlas` whose charts are `A`'s charts times circle charts through the trivialisations, and
the restricted orientation) over `restrictBase F A hK` (the subtype `K`). Its projection is `π`
(`restrict_projection_val`) and its charts are those of `F` (`restrict_trivialization_snd`).
The restriction is a product when `K` lies in one chart domain `neighborhood k`, `k ∈ K`
(`restrict_isGloballyTrivial_of_subset`, the disc piece around an extremum of RG01a). Principal
atlases restrict (`PrincipalAtlas.restrict`), so over any sub-disc the restriction of a principal
circle bundle is a product (`CircleFibration.restrict_isGloballyTrivial`).
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

section Cocycle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ} (V : Fin n → TopologicalSpace.Opens M) (g : Fin n → Fin n → M → Circle)

def CircleCocycleTrivialOn (S : Set M) : Prop :=
  ∃ h : Fin n → M → Circle, (∀ i, ContMDiffOn I (𝓡 1) ∞ (h i) (V i ∩ S)) ∧
    ∀ i j y, y ∈ V i → y ∈ V j → y ∈ S → g i j y = h i y * (h j y)⁻¹

variable {I V g}

theorem CircleCocycleTrivialOn.mono {S T : Set M} (hS : CircleCocycleTrivialOn I V g S)
    (hTS : T ⊆ S) : CircleCocycleTrivialOn I V g T := by
  obtain ⟨h, hsm, hc⟩ := hS
  exact ⟨h, fun i => (hsm i).mono (inter_subset_inter_right _ hTS),
    fun i j y hi hj hy => hc i j y hi hj (hTS hy)⟩

theorem circleCocycleTrivialOn_of_subset_empty {S : Set M} (hS : S ⊆ ∅) :
    CircleCocycleTrivialOn I V g S :=
  ⟨fun _ _ => 1, fun _ => contMDiffOn_const, fun _ _ _ _ _ hy => absurd (hS hy) (notMem_empty _)⟩

theorem circleCocycleTrivialOn_of_subset
    (hcoc : ∀ i j k y, y ∈ V i → y ∈ V j → y ∈ V k → g i j y * g j k y = g i k y)
    (hsm : ∀ i j, ContMDiffOn I (𝓡 1) ∞ (g i j) (V i ∩ V j)) {S : Set M} (m : Fin n)
    (hS : S ⊆ V m) : CircleCocycleTrivialOn I V g S :=
  ⟨fun i => g i m, fun i => (hsm i m).mono (inter_subset_inter_right _ hS),
    fun i j y hi hj hy => by
      change g i j y = g i m y * (g j m y)⁻¹
      rw [← hcoc i j m y hi hj (hS hy), mul_inv_cancel_right]⟩

private theorem circle_div_comm {a b c d : Circle} (h : a * b⁻¹ = c * d⁻¹) :
    b * d⁻¹ = a * c⁻¹ := by
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul] at h ⊢
  rw [mul_comm b, ← h, mul_comm]

theorem CircleCocycleTrivialOn.union (hcov : ∀ y, ∃ i, y ∈ V i) {S T : Set M} (hSo : IsOpen S)
    (hTo : IsOpen T) (hS : CircleCocycleTrivialOn I V g S) (hT : CircleCocycleTrivialOn I V g T)
    (hlift : ∀ φ : M → Circle, ContMDiffOn I (𝓡 1) ∞ φ (S ∩ T) →
      ∃ F : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F (S ∩ T) ∧ ∀ y ∈ S ∩ T, Circle.exp (F y) = φ y)
    (ρ : M → ℝ) (hρ : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ) (hρS : ∀ y ∈ S, y ∉ T → ρ =ᶠ[𝓝 y] 0)
    (hρT : ∀ y ∈ T, y ∉ S → ρ =ᶠ[𝓝 y] 1) : CircleCocycleTrivialOn I V g (S ∪ T) := by
  classical
  obtain ⟨hs, hsm, hsc⟩ := hS
  obtain ⟨ht, htm, htc⟩ := hT
  let ι : M → Fin n := fun y => Classical.choose (hcov y)
  have hι : ∀ y, y ∈ V (ι y) := fun y => Classical.choose_spec (hcov y)
  let φ : M → Circle := fun y => hs (ι y) y * (ht (ι y) y)⁻¹
  have hφ : ∀ i y, y ∈ V i → y ∈ S → y ∈ T → φ y = hs i y * (ht i y)⁻¹ := by
    intro i y hi hyS hyT
    have h1 := hsc i (ι y) y hi (hι y) hyS
    rw [htc i (ι y) y hi (hι y) hyT] at h1
    exact circle_div_comm h1.symm
  have hsA : ∀ i y, y ∈ V i → y ∈ S → ContMDiffAt I (𝓡 1) ∞ (hs i) y := fun i y hi hy =>
    (hsm i y ⟨hi, hy⟩).contMDiffAt (((V i).isOpen.inter hSo).mem_nhds ⟨hi, hy⟩)
  have htA : ∀ i y, y ∈ V i → y ∈ T → ContMDiffAt I (𝓡 1) ∞ (ht i) y := fun i y hi hy =>
    (htm i y ⟨hi, hy⟩).contMDiffAt (((V i).isOpen.inter hTo).mem_nhds ⟨hi, hy⟩)
  have hφsm : ContMDiffOn I (𝓡 1) ∞ φ (S ∩ T) := by
    intro y hy
    have hU : (V (ι y) : Set M) ∩ S ∩ T ∈ 𝓝 y :=
      (((V (ι y)).isOpen.inter hSo).inter hTo).mem_nhds ⟨⟨hι y, hy.1⟩, hy.2⟩
    have h1 : ContMDiffAt I (𝓡 1) ∞ (fun y' => hs (ι y) y' * (ht (ι y) y')⁻¹) y :=
      (hsA _ y (hι y) hy.1).mul (htA _ y (hι y) hy.2).inv
    refine (h1.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [hU] with y' hy'
    exact hφ _ y' hy'.1.1 hy'.1.2 hy'.2
  obtain ⟨F, hFsm, hF⟩ := hlift φ hφsm
  let uS : M → Circle := fun y => Circle.exp (ρ y * F y)
  let uT : M → Circle := fun y => Circle.exp ((ρ y - 1) * F y)
  have hkey : ∀ i y, y ∈ V i → y ∈ S → y ∈ T →
      hs i y * (uS y)⁻¹ = ht i y * (uT y)⁻¹ := by
    intro i y hi hyS hyT
    have h1 : uS y = uT y * φ y := by
      change Circle.exp (ρ y * F y) = Circle.exp ((ρ y - 1) * F y) * φ y
      rw [← hF y ⟨hyS, hyT⟩, ← Circle.exp_add]
      ring_nf
    rw [h1, hφ i y hi hyS hyT, mul_inv, mul_inv, inv_inv, mul_left_comm, mul_inv_cancel_left,
      mul_comm]
  refine ⟨fun i y => if y ∈ S then hs i y * (uS y)⁻¹ else ht i y * (uT y)⁻¹, fun i => ?_, ?_⟩
  · intro y hy
    obtain ⟨hi, hyST⟩ := hy
    refine ContMDiffAt.contMDiffWithinAt ?_
    by_cases hyS : y ∈ S
    · have huS : ContMDiffAt I (𝓡 1) ∞ uS y := by
        by_cases hyT : y ∈ T
        · have hFA : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ F y :=
            (hFsm y ⟨hyS, hyT⟩).contMDiffAt ((hSo.inter hTo).mem_nhds ⟨hyS, hyT⟩)
          exact contMDiff_circleExp.contMDiffAt.comp y ((hρ y).mul hFA)
        · refine (contMDiffAt_const (c := (1 : Circle))).congr_of_eventuallyEq ?_
          filter_upwards [hρS y hyS hyT] with y' hy'
          change Circle.exp (ρ y' * F y') = 1
          rw [hy', Pi.zero_apply, zero_mul, Circle.exp_zero]
      refine ((hsA i y hi hyS).mul huS.inv).congr_of_eventuallyEq ?_
      filter_upwards [hSo.mem_nhds hyS] with y' hy'
      exact ite_eq_left hy'
    · have hyT : y ∈ T := hyST.resolve_left hyS
      have huT : ContMDiffAt I (𝓡 1) ∞ uT y := by
        refine (contMDiffAt_const (c := (1 : Circle))).congr_of_eventuallyEq ?_
        filter_upwards [hρT y hyT hyS] with y' hy'
        change Circle.exp ((ρ y' - 1) * F y') = 1
        rw [hy', Pi.one_apply, sub_self, zero_mul, Circle.exp_zero]
      refine ((htA i y hi hyT).mul huT.inv).congr_of_eventuallyEq ?_
      filter_upwards [hTo.mem_nhds hyT, (V i).isOpen.mem_nhds hi] with y' hy' hi'
      by_cases hy'S : y' ∈ S
      · rw [ite_eq_left hy'S]
        exact hkey i y' hi' hy'S hy'
      · exact ite_eq_right hy'S
  · intro i j y hi hj hy
    by_cases hyS : y ∈ S
    · change g i j y = (if y ∈ S then _ else _) * (if y ∈ S then _ else _)⁻¹
      rw [ite_eq_left hyS, ite_eq_left hyS, hsc i j y hi hj hyS, mul_inv_rev, inv_inv, mul_assoc,
        inv_mul_cancel_left]
    · have hyT : y ∈ T := hy.resolve_left hyS
      change g i j y = (if y ∈ S then _ else _) * (if y ∈ S then _ else _)⁻¹
      rw [ite_eq_right hyS, ite_eq_right hyS, htc i j y hi hj hyT, mul_inv_rev, inv_inv, mul_assoc,
        inv_mul_cancel_left]

end Cocycle

section Lift

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

attribute [local instance] finrank_real_complex_fact'

theorem contMDiffAt_arg_mul_inv (w : Circle) :
    ContMDiffAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ (fun z : Circle => Complex.arg ((z * w⁻¹ : Circle) : ℂ)) w := by
  have hc : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun z : Circle => (z : ℂ)) := contMDiff_coe_sphere
  have h1 : ContMDiffAt (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun z : Circle => ((z * w⁻¹ : Circle) : ℂ)) w :=
    (hc.comp (contMDiff_mul_right (a := w⁻¹))).contMDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun z : ℂ => Complex.arg z) ((w * w⁻¹ : Circle) : ℂ) := by
    rw [mul_inv_cancel, Circle.coe_one]
    have h3 : (fun z : ℂ => Complex.arg z) = fun z => (Complex.log z).im :=
      funext fun z => (Complex.log_im z).symm
    rw [h3]
    exact Complex.imCLM.contDiff.contDiffAt.comp _
      ((Complex.contDiffAt_log (by simp)).restrict_scalars ℝ)
  exact ContDiffAt.comp_contMDiffAt (x := w) (f := fun z : Circle => ((z * w⁻¹ : Circle) : ℂ))
    h2 h1

theorem contMDiffOn_of_circleExp_eq {O : Set M} (hO : IsOpen O) {φ : M → Circle}
    (hφ : ContMDiffOn I (𝓡 1) ∞ φ O) {F : M → ℝ} (hF : ContinuousOn F O)
    (hFφ : ∀ y ∈ O, Circle.exp (F y) = φ y) : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O := by
  intro y hy
  have hφy : ContMDiffAt I (𝓡 1) ∞ φ y := (hφ y hy).contMDiffAt (hO.mem_nhds hy)
  let G : M → ℝ := fun y' => F y + Complex.arg ((φ y' * (φ y)⁻¹ : Circle) : ℂ)
  have hG : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ G y :=
    contMDiffAt_const.add ((contMDiffAt_arg_mul_inv (φ y)).comp y hφy)
  have hGy : G y = F y := by
    change F y + Complex.arg ((φ y * (φ y)⁻¹ : Circle) : ℂ) = F y
    rw [mul_inv_cancel, Circle.coe_one, Complex.arg_one, add_zero]
  have hcont : ContinuousAt (fun y' => F y' - G y') y :=
    ((hF y hy).continuousAt (hO.mem_nhds hy)).sub hG.continuousAt
  have hsmall : ∀ᶠ y' in 𝓝 y, F y' - G y' ∈ Metric.ball (0 : ℝ) (2 * Real.pi) := by
    have h0 : F y - G y = 0 := by rw [hGy, sub_self]
    refine hcont.preimage_mem_nhds ?_
    rw [h0]
    exact Metric.ball_mem_nhds 0 Real.two_pi_pos
  refine (hG.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hsmall, hO.mem_nhds hy] with y' hy' hy'O
  have hexp : Circle.exp (F y') = Circle.exp (G y') := by
    change Circle.exp (F y') = Circle.exp (F y + Complex.arg ((φ y' * (φ y)⁻¹ : Circle) : ℂ))
    rw [Circle.exp_add, Circle.exp_arg, hFφ y' hy'O, hFφ y hy, mul_comm, inv_mul_cancel_right]
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hexp
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, hm, add_sub_cancel_left, abs_mul,
    abs_of_pos Real.two_pi_pos] at hy'
  have hm1 : |(m : ℝ)| < 1 := by
    have h := Real.two_pi_pos
    nlinarith
  have hm0 : m = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hm1)
  rw [hm, hm0, Int.cast_zero, zero_mul, add_zero]

theorem exists_continuousOn_circleExp_lift [LocallyPathConnectedSpace M] {O : Set M}
    (hO : IsOpen O) (hsc : IsSimplyConnected O) {φ : M → Circle} (hφ : ContinuousOn φ O) :
    ∃ F : M → ℝ, ContinuousOn F O ∧ ∀ y ∈ O, Circle.exp (F y) = φ y := by
  obtain ⟨f, hfc, hf⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc hO
    (g := fun y => (φ y : ℂ)) (continuous_subtype_val.comp_continuousOn hφ)
    (by
      rintro ⟨y, -, hy⟩
      exact Circle.coe_ne_zero _ hy)
  refine ⟨fun y => (f y).im, Complex.continuous_im.comp_continuousOn hfc, fun y hy => ?_⟩
  have h1 : Complex.exp (f y) = φ y := hf hy
  have h2 : (f y).re = 0 := by
    have h3 := congrArg (fun z : ℂ => ‖z‖) h1
    simp only [Complex.norm_exp, Circle.norm_coe] at h3
    exact Real.exp_eq_one_iff _ |>.mp h3
  apply Subtype.ext
  change Complex.exp (((f y).im : ℂ) * Complex.I) = φ y
  rw [← h1]
  congr 1
  apply Complex.ext <;> simp [h2]

theorem exists_contMDiffOn_circleExp_lift_of_convex [LocallyPathConnectedSpace M] {ε : M → ℂ}
    (hε : _root_.Topology.IsEmbedding ε) (hD : Convex ℝ (range ε)) {O : Set ℂ} (hO : IsOpen O)
    (hOc : Convex ℝ O) {φ : M → Circle} (hφ : ContMDiffOn I (𝓡 1) ∞ φ (ε ⁻¹' O)) :
    ∃ F : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F (ε ⁻¹' O) ∧
      ∀ y ∈ ε ⁻¹' O, Circle.exp (F y) = φ y := by
  have hKo : IsOpen (ε ⁻¹' O) := hO.preimage hε.continuous
  rcases (ε ⁻¹' O).eq_empty_or_nonempty with hK | hK
  · refine ⟨fun _ => 0, contMDiffOn_const, fun y hy => ?_⟩
    rw [hK] at hy
    exact absurd hy (notMem_empty y)
  have hconv : Convex ℝ (ε '' (ε ⁻¹' O)) := by
    rw [image_preimage_eq_inter_range]
    exact hOc.inter hD
  have : ContractibleSpace (ε '' (ε ⁻¹' O)) := hconv.contractibleSpace (hK.image ε)
  have : ContractibleSpace (ε ⁻¹' O) := (hε.homeomorphImage (ε ⁻¹' O)).contractibleSpace
  have hsc : IsSimplyConnected (ε ⁻¹' O) := inferInstanceAs (SimplyConnectedSpace (ε ⁻¹' O))
  obtain ⟨F, hFc, hF⟩ := exists_continuousOn_circleExp_lift hKo hsc hφ.continuousOn
  exact ⟨F, contMDiffOn_of_circleExp_eq hKo hφ hFc hF, hF⟩

end Lift


section Sweep

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ} {V : Fin n → TopologicalSpace.Opens M} {g : Fin n → Fin n → M → Circle}

def discSweepSlab (ℓ : ℂ →L[ℝ] ℝ) (a b : ℝ) : Set ℂ := {z | a < ℓ z ∧ ℓ z < b}

theorem isOpen_discSweepSlab (ℓ : ℂ →L[ℝ] ℝ) (a b : ℝ) : IsOpen (discSweepSlab ℓ a b) :=
  (isOpen_lt continuous_const ℓ.continuous).inter (isOpen_lt ℓ.continuous continuous_const)

theorem convex_discSweepSlab (ℓ : ℂ →L[ℝ] ℝ) (a b : ℝ) : Convex ℝ (discSweepSlab ℓ a b) :=
  (convex_halfSpace_gt ℓ.toLinearMap.isLinear a).inter
    (convex_halfSpace_lt ℓ.toLinearMap.isLinear b)

def discSweepCutoff (c s t : ℝ) : ℝ := Real.smoothTransition ((t - (c - 2 * s / 3)) * (3 / s))

theorem contDiff_discSweepCutoff (c s : ℝ) : ContDiff ℝ ∞ (discSweepCutoff c s) :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp
    ((contDiff_id.sub contDiff_const).mul contDiff_const)

theorem discSweepCutoff_eq_zero {c s t : ℝ} (hs : 0 < s) (ht : t ≤ c - 2 * s / 3) :
    discSweepCutoff c s t = 0 :=
  Real.smoothTransition.zero_of_nonpos
    (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))

theorem discSweepCutoff_eq_one {c s t : ℝ} (hs : 0 < s) (ht : c - s / 3 ≤ t) :
    discSweepCutoff c s t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have h1 : s / 3 ≤ t - (c - 2 * s / 3) := by linarith
  calc (1 : ℝ) = s / 3 * (3 / s) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)

variable [LocallyPathConnectedSpace M]

theorem CircleCocycleTrivialOn.sweep_step (hcov : ∀ y, ∃ i, y ∈ V i) {ε : M → ℂ}
    (hε : _root_.Topology.IsEmbedding ε) (hεs : ContMDiff I 𝓘(ℝ, ℂ) ∞ ε)
    (hD : Convex ℝ (range ε)) (ℓ : ℂ →L[ℝ] ℝ) {Q : Set ℂ} (hQ : IsOpen Q) (hQc : Convex ℝ Q)
    {s : ℝ} (hs : 0 < s) (c : ℝ)
    (hS : CircleCocycleTrivialOn I V g (ε ⁻¹' (Q ∩ {z | ℓ z < c})))
    (hT : CircleCocycleTrivialOn I V g (ε ⁻¹' (Q ∩ discSweepSlab ℓ (c - s) (c + s)))) :
    CircleCocycleTrivialOn I V g (ε ⁻¹' (Q ∩ {z | ℓ z < c + s})) := by
  have hℓε : Continuous fun y => ℓ (ε y) := ℓ.continuous.comp hε.continuous
  have hSo : IsOpen (ε ⁻¹' (Q ∩ {z | ℓ z < c})) :=
    (hQ.inter (isOpen_lt ℓ.continuous continuous_const)).preimage hε.continuous
  have hTo : IsOpen (ε ⁻¹' (Q ∩ discSweepSlab ℓ (c - s) (c + s))) :=
    (hQ.inter (isOpen_discSweepSlab ℓ _ _)).preimage hε.continuous
  have hST : ε ⁻¹' (Q ∩ {z | ℓ z < c}) ∩ ε ⁻¹' (Q ∩ discSweepSlab ℓ (c - s) (c + s)) =
      ε ⁻¹' (Q ∩ discSweepSlab ℓ (c - s) c) := by
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, discSweepSlab]
    constructor
    · rintro ⟨⟨hq, h1⟩, -, h2, -⟩
      exact ⟨hq, h2, h1⟩
    · rintro ⟨hq, h1, h2⟩
      exact ⟨⟨hq, h2⟩, hq, h1, by linarith⟩
  refine (hS.union hcov hSo hTo hT ?_ (fun y => discSweepCutoff c s (ℓ (ε y)))
    ((contDiff_discSweepCutoff c s).comp_contMDiff (ℓ.contDiff.comp_contMDiff hεs)) ?_ ?_).mono ?_
  · intro φ hφ
    rw [hST] at hφ ⊢
    exact exists_contMDiffOn_circleExp_lift_of_convex hε hD (hQ.inter (isOpen_discSweepSlab ℓ _ _))
      (hQc.inter (convex_discSweepSlab ℓ _ _)) hφ
  · intro y hyS hyT
    have hy : ℓ (ε y) ≤ c - s := by
      by_contra hlt
      exact hyT ⟨hyS.1, by linarith, by linarith [hyS.2.out]⟩
    filter_upwards [(isOpen_lt hℓε continuous_const).mem_nhds
      (show ℓ (ε y) < c - 2 * s / 3 by linarith)] with y' hy'
    exact discSweepCutoff_eq_zero hs (le_of_lt hy')
  · intro y hyT hyS
    have hy : c ≤ ℓ (ε y) := by
      by_contra hlt
      exact hyS ⟨hyT.1, not_le.mp hlt⟩
    filter_upwards [(isOpen_lt continuous_const hℓε).mem_nhds
      (show c - s / 3 < ℓ (ε y) by linarith)] with y' hy'
    exact discSweepCutoff_eq_one hs (le_of_lt hy')
  · intro y hy
    by_cases h : ℓ (ε y) < c
    · exact Or.inl ⟨hy.1, h⟩
    · exact Or.inr ⟨hy.1, by linarith [hs], hy.2.out⟩

theorem CircleCocycleTrivialOn.sweep (hcov : ∀ y, ∃ i, y ∈ V i) {ε : M → ℂ}
    (hε : _root_.Topology.IsEmbedding ε) (hεs : ContMDiff I 𝓘(ℝ, ℂ) ∞ ε)
    (hD : Convex ℝ (range ε)) (ℓ : ℂ →L[ℝ] ℝ) {R : ℝ} (hR : ∀ y, |ℓ (ε y)| < R) {Q : Set ℂ}
    (hQ : IsOpen Q) (hQc : Convex ℝ Q) {s : ℝ} (hs : 0 < s)
    (hpiece : ∀ c, CircleCocycleTrivialOn I V g (ε ⁻¹' (Q ∩ discSweepSlab ℓ (c - s) (c + s)))) :
    CircleCocycleTrivialOn I V g (ε ⁻¹' Q) := by
  have hk : ∀ k : ℕ, CircleCocycleTrivialOn I V g (ε ⁻¹' (Q ∩ {z | ℓ z < -R + k * s})) := by
    intro k
    induction k with
    | zero =>
      refine circleCocycleTrivialOn_of_subset_empty fun y hy => ?_
      have h1 := hy.2.out
      have h2 := (abs_lt.mp (hR y)).1
      simp only [CharP.cast_eq_zero, zero_mul, add_zero] at h1
      linarith
    | succ k ih =>
      have h := ih.sweep_step hcov hε hεs hD ℓ hQ hQc hs _ (hpiece _)
      have hc : -R + (k : ℝ) * s + s = -R + ((k + 1 : ℕ) : ℝ) * s := by
        push_cast
        ring
      rwa [hc] at h
  obtain ⟨k, hk'⟩ := exists_nat_ge (2 * R / s)
  refine (hk k).mono fun y hy => ⟨hy, ?_⟩
  have h1 := (abs_lt.mp (hR y)).2
  have h2 : 2 * R ≤ k * s := (div_le_iff₀ hs).mp hk'
  change ℓ (ε y) < -R + k * s
  linarith

end Sweep

section Disc

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ} {V : Fin n → TopologicalSpace.Opens M} {g : Fin n → Fin n → M → Circle}

theorem exists_lebesgue_number_preimage_ball [CompactSpace M] {ε : M → ℂ}
    (hε : _root_.Topology.IsEmbedding ε) (hcov : ∀ y, ∃ i, y ∈ V i) :
    ∃ δ > 0, ∀ y, ∃ i, ε ⁻¹' Metric.ball (ε y) δ ⊆ V i := by
  have hc : ∀ i, ∃ t : Set ℂ, IsOpen t ∧ ε ⁻¹' t = V i := fun i =>
    hε.isInducing.isOpen_iff.mp (V i).isOpen
  choose c hco hcV using hc
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (isCompact_range hε.continuous) hco
    (by
      rintro _ ⟨y, rfl⟩
      obtain ⟨i, hi⟩ := hcov y
      have hi' : y ∈ (V i : Set M) := hi
      rw [← hcV i] at hi'
      exact mem_iUnion.mpr ⟨i, hi'⟩)
  refine ⟨δ, hδ, fun y => ?_⟩
  obtain ⟨i, hi⟩ := hball (ε y) (mem_range_self y)
  refine ⟨i, fun y' hy' => ?_⟩
  rw [← hcV i]
  exact hi hy'

theorem circleCocycleTrivialOn_of_diam_lt
    (hcoc : ∀ i j k y, y ∈ V i → y ∈ V j → y ∈ V k → g i j y * g j k y = g i k y)
    (hsm : ∀ i j, ContMDiffOn I (𝓡 1) ∞ (g i j) (V i ∩ V j)) {ε : M → ℂ} {δ : ℝ}
    (hδ : ∀ y, ∃ i, ε ⁻¹' Metric.ball (ε y) δ ⊆ V i) {A : Set ℂ}
    (hA : ∀ z ∈ A, ∀ w ∈ A, ‖z - w‖ < δ) : CircleCocycleTrivialOn I V g (ε ⁻¹' A) := by
  rcases (ε ⁻¹' A).eq_empty_or_nonempty with hK | ⟨y, hy⟩
  · exact circleCocycleTrivialOn_of_subset_empty hK.subset
  obtain ⟨i, hi⟩ := hδ y
  refine circleCocycleTrivialOn_of_subset hcoc hsm i fun y' hy' => hi ?_
  rw [mem_preimage, Metric.mem_ball, dist_eq_norm]
  exact hA _ hy' _ hy

theorem circleCocycleTrivialOn_univ [CompactSpace M] [LocallyPathConnectedSpace M]
    (hcov : ∀ y, ∃ i, y ∈ V i)
    (hcoc : ∀ i j k y, y ∈ V i → y ∈ V j → y ∈ V k → g i j y * g j k y = g i k y)
    (hsm : ∀ i j, ContMDiffOn I (𝓡 1) ∞ (g i j) (V i ∩ V j)) {ε : M → ℂ}
    (hε : _root_.Topology.IsEmbedding ε) (hεs : ContMDiff I 𝓘(ℝ, ℂ) ∞ ε)
    (hD : Convex ℝ (range ε)) {R : ℝ} (hR : ∀ y, ‖ε y‖ < R) :
    CircleCocycleTrivialOn I V g univ := by
  obtain ⟨δ, hδ, hleb⟩ := exists_lebesgue_number_preimage_ball hε hcov
  have hs : 0 < δ / 4 := by positivity
  have hre : ∀ y, |Complex.reCLM (ε y)| < R := fun y =>
    lt_of_le_of_lt (Complex.abs_re_le_norm _) (hR y)
  have him : ∀ y, |Complex.imCLM (ε y)| < R := fun y =>
    lt_of_le_of_lt (Complex.abs_im_le_norm _) (hR y)
  have hrow : ∀ c, CircleCocycleTrivialOn I V g
      (ε ⁻¹' (univ ∩ discSweepSlab Complex.imCLM (c - δ / 4) (c + δ / 4))) := by
    intro c
    refine CircleCocycleTrivialOn.sweep hcov hε hεs hD Complex.reCLM hre
      (isOpen_univ.inter (isOpen_discSweepSlab _ _ _))
      (convex_univ.inter (convex_discSweepSlab _ _ _)) hs
      fun c' => circleCocycleTrivialOn_of_diam_lt hcoc hsm hleb ?_
    rintro z ⟨⟨-, hz1, hz2⟩, hz3, hz4⟩ w ⟨⟨-, hw1, hw2⟩, hw3, hw4⟩
    simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hz1 hz2 hz3 hz4 hw1 hw2 hw3 hw4
    calc ‖z - w‖ ≤ |(z - w).re| + |(z - w).im| := Complex.norm_le_abs_re_add_abs_im _
      _ < δ / 2 + δ / 2 := by
        rw [Complex.sub_re, Complex.sub_im]
        exact add_lt_add (abs_lt.mpr ⟨by linarith, by linarith⟩)
          (abs_lt.mpr ⟨by linarith, by linarith⟩)
      _ = δ := by ring
  have h := CircleCocycleTrivialOn.sweep hcov hε hεs hD Complex.imCLM him isOpen_univ convex_univ
    hs hrow
  rwa [preimage_univ] at h

end Disc

theorem locallyPathConnectedSpace_surfaceModel (k : SurfaceModel) :
    LocallyPathConnectedSpace (SurfaceModel.Space k) := by
  cases k
  · exact inferInstanceAs (LocallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)))
  · exact inferInstanceAs (LocallyPathConnectedSpace (EuclideanHalfSpace 2))

theorem discCircleCocycleTrivial : DiscCircleCocycleTrivial.{u} := by
  intro B P ⟨e⟩ n V hcov g hsm hcoc
  have : LocallyPathConnectedSpace (SurfaceModel.Space B.kind) :=
    locallyPathConnectedSpace_surfaceModel B.kind
  have : LocallyPathConnectedSpace B.Carrier :=
    ChartedSpace.locallyPathConnectedSpace (SurfaceModel.Space B.kind) B.Carrier
  let ε : B.Carrier → ℂ := fun y => P.embedding (e y)
  have hε : _root_.Topology.IsEmbedding ε :=
    P.isSmoothEmbedding.isEmbedding.comp e.toHomeomorph.isEmbedding
  have hεs : ContMDiff (SurfaceModel.model B.kind) 𝓘(ℝ, ℂ) ∞ ε :=
    P.isSmoothEmbedding.contMDiff.comp e.contMDiff
  have hrange : range ε = Metric.closedBall 0 3 := by
    rw [← planarModel_one, ← P.range_embedding]
    exact e.surjective.range_comp P.embedding
  have hD : Convex ℝ (range ε) := hrange ▸ convex_closedBall 0 3
  have hR : ∀ y, ‖ε y‖ < 4 := fun y => by
    have h1 : ε y ∈ Metric.closedBall (0 : ℂ) 3 := hrange ▸ mem_range_self y
    rw [mem_closedBall_zero_iff] at h1
    linarith
  obtain ⟨h, hh, hc⟩ := circleCocycleTrivialOn_univ hcov hcoc hsm hε hεs hD hR
  exact ⟨h, fun i => by simpa only [inter_univ] using hh i,
    fun i j y hi hj => hc i j y hi hj trivial⟩

section DiscConsequences

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}

theorem PrincipalAtlas.isGloballyTrivial_of_planarBase {F : CircleFibration C U}
    (PA : PrincipalAtlas F) (P : PlanarBase.{u} 1)
    (e : F.base.Carrier ≃ₘ⟮SurfaceModel.model F.base.kind,
      SurfaceModel.model P.surface.kind⟯ P.surface.Carrier) :
    CircleFibration.IsGloballyTrivial F :=
  PA.isGloballyTrivial discCircleCocycleTrivial P e

theorem circleBundlesOverDiscStandard_iff_nonempty_principalAtlas :
    CircleBundlesOverDiscStandard.{u} ↔
      ∀ (C : CompactCarrier.{u}) (U : TopologicalSpace.Opens C.Carrier)
        (F : CircleFibration C U) (P : PlanarBase.{u} 1),
        Nonempty (F.base.Carrier ≃ₘ⟮SurfaceModel.model F.base.kind,
          SurfaceModel.model P.surface.kind⟯ P.surface.Carrier) → Nonempty (PrincipalAtlas F) :=
  circleBundlesOverDiscStandard_iff_principalAtlas discCircleCocycleTrivial

end DiscConsequences

def fibreChartLinearEquiv :
    (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (((SmoothBoundaryAtlas.firstCoordinateEquiv 1).symm.prodCongr
      (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 1)))).trans
    (ContinuousLinearEquiv.prodAssoc ℝ ℝ _ _)).trans
    (((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
      (ContinuousLinearEquiv.ofFinrankEq (by simp))).trans
      (SmoothBoundaryAtlas.firstCoordinateEquiv 2))

theorem fibreChartLinearEquiv_apply_zero
    (p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) :
    fibreChartLinearEquiv p 0 = p.1 0 := by
  change SmoothBoundaryAtlas.firstCoordinateEquiv 2 _ 0 = _
  rw [SmoothBoundaryAtlas.firstCoordinateEquiv_apply_zero]
  conv_rhs => rw [← (SmoothBoundaryAtlas.firstCoordinateEquiv 1).apply_symm_apply p.1]
  rfl

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}

theorem CircleFibration.exists_productChart (F : CircleFibration C U) {K : Set F.base.Carrier}
    (A : SmoothBoundaryAtlas (SurfaceModel.model F.base.kind) 2 K) (x : U)
    (hx : F.projection x ∈ K) :
    ∃ Φ : PartialDiffeomorph C.model 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))
        U (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) ∞,
      x ∈ Φ.source ∧ ∀ y ∈ Φ.source, F.projection y ∈ (A.ambientChart ⟨_, hx⟩).source ∧
        (Φ y).1 = A.ambientChart ⟨_, hx⟩ (F.projection y) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  let b := F.projection x
  let φ := A.ambientChart ⟨b, hx⟩
  let N := F.neighborhood b
  let W := TopologicalSpace.Opens.comap F.projection N
  have hxW : x ∈ W := F.mem_neighborhood b
  let τ := F.trivialization b
  let θ := (τ ⟨x, hxW⟩).2
  let χ := PartialDiffeomorph.extendedChart (I := 𝓡 1) θ
  let ιW := PartialDiffeomorph.subtypeVal (I := C.model) W ⟨⟨x, hxW⟩⟩
  let Ψ := (τ.toPartialDiffeomorph.trans
    (((PartialDiffeomorph.subtypeVal (I := SurfaceModel.model F.base.kind) N
      ⟨⟨b, F.mem_neighborhood b⟩⟩).prod
      (Diffeomorph.refl (𝓡 1) Circle ∞).toPartialDiffeomorph).trans (φ.prod χ)))
  let Φ := ιW.symm.trans Ψ
  have hb : b ∈ φ.source := A.mem_source ⟨b, hx⟩
  have hWt : ιW.target = W := TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target W _
  have hsymm : ∀ y : U, ∀ hy : y ∈ W, ιW.symm y = ⟨y, hy⟩ := by
    intro y hy
    apply Subtype.ext
    exact ιW.toPartialEquiv.right_inv' (by rw [hWt]; exact hy)
  refine ⟨Φ, ?_, ?_⟩
  · have h1 : x ∈ ιW.symm.source := by
      change x ∈ ιW.target
      rw [hWt]
      exact hxW
    have hb' : ((τ ⟨x, hxW⟩).1 : F.base.Carrier) ∈ φ.source := by
      rw [F.projection_trivialization]
      exact hb
    have h2 : (⟨x, hxW⟩ : W) ∈ Ψ.source :=
      ⟨trivial, ⟨trivial, trivial⟩, hb', mem_extChartAt_source θ⟩
    have h3 : ιW.symm x ∈ Ψ.source := by
      rw [hsymm x hxW]
      exact h2
    exact ⟨h1, h3⟩
  · intro y hy
    have hyW : y ∈ W := by
      have h1 : y ∈ ιW.target := hy.1
      rw [hWt] at h1
      exact h1
    have h2 : ιW.symm y ∈ Ψ.source := hy.2
    rw [hsymm y hyW] at h2
    have hπ : ((τ ⟨y, hyW⟩).1 : F.base.Carrier) = F.projection y := F.projection_trivialization b _
    have h3 : ((τ ⟨y, hyW⟩).1 : F.base.Carrier) ∈ φ.source := h2.2.2.1
    rw [hπ] at h3
    refine ⟨h3, ?_⟩
    change φ (((τ (ιW.symm y)).1 : F.base.Carrier)) = φ (F.projection y)
    rw [hsymm y hyW, hπ]

theorem CircleFibration.exists_totalChart (F : CircleFibration C U) {K : Set F.base.Carrier}
    (A : SmoothBoundaryAtlas (SurfaceModel.model F.base.kind) 2 K) (x : F.projection ⁻¹' K) :
    ∃ Ψ : PartialDiffeomorph C.model 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) U
        (EuclideanSpace ℝ (Fin 3)) ∞,
      x.val ∈ Ψ.source ∧ ∀ y ∈ Ψ.source, y ∈ F.projection ⁻¹' K ↔ 0 ≤ Ψ y 0 := by
  obtain ⟨Φ, hxΦ, hΦ⟩ := CircleFibration.exists_productChart F A x.val x.2
  let L := SmoothBoundaryAtlas.affineDiffeomorph fibreChartLinearEquiv 0
  refine ⟨Φ.trans L.toPartialDiffeomorph, ⟨hxΦ, trivial⟩, fun y hy => ?_⟩
  obtain ⟨hsrc, hval⟩ := hΦ y hy.1
  have h0 : (Φ.trans L.toPartialDiffeomorph) y 0 =
      A.ambientChart ⟨_, x.2⟩ (F.projection y) 0 := by
    change (fibreChartLinearEquiv (Φ y) + 0) 0 = _
    rw [add_zero, fibreChartLinearEquiv_apply_zero, hval]
  rw [h0]
  exact A.mem_iff ⟨_, x.2⟩ (F.projection y) hsrc

def CircleFibration.totalAtlas (F : CircleFibration C U) {K : Set F.base.Carrier}
    (A : SmoothBoundaryAtlas (SurfaceModel.model F.base.kind) 2 K) :
    SmoothBoundaryAtlas C.model 3 (F.projection ⁻¹' K) where
  ambientChart x := Classical.choose (CircleFibration.exists_totalChart F A x)
  mem_source x := (Classical.choose_spec (CircleFibration.exists_totalChart F A x)).1
  mem_iff x := (Classical.choose_spec (CircleFibration.exists_totalChart F A x)).2

theorem CircleFibration.isCompact_preimage (F : CircleFibration C U) {K : Set F.base.Carrier}
    (hK : IsClosed K) : IsCompact (F.projection ⁻¹' K) := by
  have hloc : ∀ k ∈ K, ∃ L ∈ 𝓝 k, L ⊆ F.neighborhood k ∧ IsCompact L := fun k _ =>
    local_compact_nhds (CircleFibration.neighborhood_mem_nhds F k)
  choose! L hLn hLs hLc using hloc
  obtain ⟨t, htK, hcov⟩ := hK.isCompact.elim_nhds_subcover L hLn
  let img : F.base.Carrier → Set U := fun k =>
    (fun q => ((F.trivialization k).symm q).val) ''
      ((Subtype.val ⁻¹' L k : Set (F.neighborhood k)) ×ˢ univ)
  have himg : ∀ k ∈ t, IsCompact (img k) := by
    intro k hk
    have h1 : IsCompact (Subtype.val ⁻¹' L k : Set (F.neighborhood k)) := by
      rw [Subtype.isCompact_iff, image_preimage_eq_inter_range, Subtype.range_coe,
        inter_eq_left.mpr (hLs k (htK k hk))]
      exact hLc k (htK k hk)
    exact (h1.prod isCompact_univ).image
      (continuous_subtype_val.comp (F.trivialization k).symm.continuous)
  refine (t.isCompact_biUnion himg).of_isClosed_subset
    (hK.preimage F.projection.continuous) fun y hy => ?_
  obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.mp (hcov hy)
  have hyN : F.projection y ∈ F.neighborhood k := hLs k (htK k hk) hyk
  refine mem_iUnion₂.mpr ⟨k, hk, ⟨F.trivialization k ⟨y, hyN⟩, ⟨?_, trivial⟩, ?_⟩⟩
  · change ((F.trivialization k ⟨y, hyN⟩).1 : F.base.Carrier) ∈ L k
    rw [F.projection_trivialization]
    exact hyk
  · change (((F.trivialization k).symm (F.trivialization k ⟨y, hyN⟩)) : U) = y
    rw [Diffeomorph.symm_apply_apply]

variable (F : CircleFibration C U) {K : Set F.base.Carrier}
  (A : SmoothBoundaryAtlas (SurfaceModel.model F.base.kind) 2 K) (hK : IsClosed K)

def CircleFibration.restrictBase [ConnectedSpace K] : CompactSurface.{u} where
  kind := .withBoundary
  Carrier := K
  charts := A.toChartedSpace
  smooth := A.isManifold
  compact := isCompact_iff_compactSpace.mp hK.isCompact

def CircleFibration.restrictTotal : CompactCarrier.{u} where
  kind := .withBoundary
  Carrier := F.projection ⁻¹' K
  charts := (CircleFibration.totalAtlas F A).toChartedSpace
  smooth := (CircleFibration.totalAtlas F A).isManifold
  compact := isCompact_iff_compactSpace.mp (CircleFibration.isCompact_preimage F hK)
  orientation := (CircleFibration.totalAtlas F A).orientation (C.orientation.restrictOpen U)

theorem CircleFibration.contMDiff_restrictTotal_val :
    ContMDiff (CircleFibration.restrictTotal F A hK).model C.model ∞
      (fun z : (CircleFibration.restrictTotal F A hK).Carrier => z.val) :=
  (CircleFibration.totalAtlas F A).contMDiff_subtype_val

theorem CircleFibration.contMDiff_restrictTotal_iff {E' H' X : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace X]
    [ChartedSpace H' X] (f : X → (CircleFibration.restrictTotal F A hK).Carrier) :
    ContMDiff J (CircleFibration.restrictTotal F A hK).model ∞ f ↔
      ContMDiff J C.model ∞ (fun x => (f x).val) :=
  (CircleFibration.totalAtlas F A).contMDiff_iff_subtype_val f

section Restrict

variable [ConnectedSpace K]

def CircleFibration.restrictProjection :
    C(↥(⊤ : TopologicalSpace.Opens (CircleFibration.restrictTotal F A hK).Carrier),
      (CircleFibration.restrictBase F A hK).Carrier) :=
  ⟨fun z => ⟨F.projection z.val.val, z.val.2⟩,
    (F.projection.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk
      _⟩

def CircleFibration.restrictOpen (N : TopologicalSpace.Opens F.base.Carrier) :
    TopologicalSpace.Opens (CircleFibration.restrictBase F A hK).Carrier :=
  ⟨Subtype.val ⁻¹' (N : Set F.base.Carrier), N.isOpen.preimage continuous_subtype_val⟩

theorem CircleFibration.contMDiff_restrictBase_val :
    ContMDiff (SurfaceModel.model (CircleFibration.restrictBase F A hK).kind)
      (SurfaceModel.model F.base.kind) ∞
      (fun z : (CircleFibration.restrictBase F A hK).Carrier => z.val) :=
  A.contMDiff_subtype_val

theorem CircleFibration.contMDiff_restrictBase_iff {E' H' X : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace X]
    [ChartedSpace H' X] (f : X → (CircleFibration.restrictBase F A hK).Carrier) :
    ContMDiff J (SurfaceModel.model (CircleFibration.restrictBase F A hK).kind) ∞ f ↔
      ContMDiff J (SurfaceModel.model F.base.kind) ∞ (fun x => (f x).val) :=
  A.contMDiff_iff_subtype_val f

def CircleFibration.restrictLocalChart (N : TopologicalSpace.Opens F.base.Carrier)
    (τ : TopologicalSpace.Opens.comap F.projection N ≃ₘ⟮C.model,
      (SurfaceModel.model F.base.kind).prod (𝓡 1)⟯ (N × Circle))
    (hτ : ∀ x, ((τ x).1 : F.base.Carrier) = F.projection x.val) :
    TopologicalSpace.Opens.comap (CircleFibration.restrictProjection F A hK)
        (CircleFibration.restrictOpen F A hK N) ≃ₘ⟮(CircleFibration.restrictTotal F A hK).model,
      (SurfaceModel.model (CircleFibration.restrictBase F A hK).kind).prod (𝓡 1)⟯
      (CircleFibration.restrictOpen F A hK N × Circle) where
  toFun z := (⟨⟨F.projection z.val.val.val, z.val.val.2⟩, z.2⟩, (τ ⟨z.val.val.val, z.2⟩).2)
  invFun q := ⟨⟨⟨(τ.symm (⟨q.1.val.val, q.1.2⟩, q.2)).val, by
      change F.projection _ ∈ K
      rw [← hτ, Diffeomorph.apply_symm_apply]
      exact q.1.val.2⟩, trivial⟩, by
    change F.projection _ ∈ N
    rw [← hτ, Diffeomorph.apply_symm_apply]
    exact q.1.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    have h : ((⟨F.projection z.val.val.val, z.2⟩ : N), (τ ⟨z.val.val.val, z.2⟩).2) =
        τ ⟨z.val.val.val, z.2⟩ :=
      Prod.ext (Subtype.ext (hτ ⟨z.val.val.val, z.2⟩).symm) rfl
    change (τ.symm (_, _)).val = _
    rw [h, Diffeomorph.symm_apply_apply]
  right_inv q := by
    have h : (⟨(τ.symm (⟨q.1.val.val, q.1.2⟩, q.2)).val, by
        change F.projection _ ∈ N
        rw [← hτ, Diffeomorph.apply_symm_apply]
        exact q.1.2⟩ : TopologicalSpace.Opens.comap F.projection N) =
        τ.symm (⟨q.1.val.val, q.1.2⟩, q.2) := rfl
    refine Prod.ext (Subtype.ext (Subtype.ext ?_)) ?_
    · change F.projection (τ.symm _).val = _
      rw [← hτ, Diffeomorph.apply_symm_apply]
    · change (τ _).2 = q.2
      rw [h, Diffeomorph.apply_symm_apply]
  contMDiff_toFun := by
    have hval : ContMDiff (CircleFibration.restrictTotal F A hK).model C.model ∞
        (fun z : TopologicalSpace.Opens.comap (CircleFibration.restrictProjection F A hK)
          (CircleFibration.restrictOpen F A hK N) => z.val.val.val) :=
      (CircleFibration.contMDiff_restrictTotal_val F A hK).comp
        (contMDiff_subtype_val.comp contMDiff_subtype_val)
    refine ContMDiff.prodMk ?_ ?_
    · apply (ContMDiff.subtypeVal_comp_iff _ _).mp
      exact (CircleFibration.contMDiff_restrictBase_iff F A hK _).mpr (F.smooth.comp hval)
    · have hι : ContMDiff (CircleFibration.restrictTotal F A hK).model C.model ∞
          (fun z : TopologicalSpace.Opens.comap (CircleFibration.restrictProjection F A hK)
            (CircleFibration.restrictOpen F A hK N) =>
            (⟨z.val.val.val, z.2⟩ : TopologicalSpace.Opens.comap F.projection N)) :=
        (ContMDiff.subtypeVal_comp_iff _ _).mp hval
      exact contMDiff_snd.comp (τ.contMDiff.comp hι)
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    apply (CircleFibration.contMDiff_restrictTotal_iff F A hK _).mpr
    have h1 : ContMDiff ((SurfaceModel.model (CircleFibration.restrictBase F A hK).kind).prod
        (𝓡 1)) (SurfaceModel.model F.base.kind) ∞
        (fun q : CircleFibration.restrictOpen F A hK N × Circle => q.1.val.val) :=
      (CircleFibration.contMDiff_restrictBase_val F A hK).comp
        (contMDiff_subtype_val.comp contMDiff_fst)
    have h2 : ContMDiff ((SurfaceModel.model (CircleFibration.restrictBase F A hK).kind).prod
        (𝓡 1)) (SurfaceModel.model F.base.kind) ∞
        (fun q : CircleFibration.restrictOpen F A hK N × Circle =>
          (⟨q.1.val.val, q.1.2⟩ : N)) :=
      (ContMDiff.subtypeVal_comp_iff _ _).mp h1
    exact contMDiff_subtype_val.comp (τ.symm.contMDiff.comp (h2.prodMk contMDiff_snd))

theorem CircleFibration.restrictLocalChart_snd (N : TopologicalSpace.Opens F.base.Carrier)
    (τ : TopologicalSpace.Opens.comap F.projection N ≃ₘ⟮C.model,
      (SurfaceModel.model F.base.kind).prod (𝓡 1)⟯ (N × Circle))
    (hτ : ∀ x, ((τ x).1 : F.base.Carrier) = F.projection x.val)
    (z : TopologicalSpace.Opens.comap (CircleFibration.restrictProjection F A hK)
      (CircleFibration.restrictOpen F A hK N)) :
    (CircleFibration.restrictLocalChart F A hK N τ hτ z).2 = (τ ⟨z.val.val.val, z.2⟩).2 :=
  rfl

def CircleFibration.restrict : CircleFibration (CircleFibration.restrictTotal F A hK) ⊤ where
  base := CircleFibration.restrictBase F A hK
  projection := CircleFibration.restrictProjection F A hK
  surjective k := by
    obtain ⟨x, hx⟩ := F.surjective k.val
    have hxK : x ∈ F.projection ⁻¹' K := by
      change F.projection x ∈ K
      rw [hx]
      exact k.2
    exact ⟨⟨⟨x, hxK⟩, trivial⟩, Subtype.ext hx⟩
  smooth := (CircleFibration.contMDiff_restrictBase_iff F A hK _).mpr
    (F.smooth.comp ((CircleFibration.contMDiff_restrictTotal_val F A hK).comp
      contMDiff_subtype_val))
  neighborhood k := CircleFibration.restrictOpen F A hK (F.neighborhood k.val)
  mem_neighborhood k := F.mem_neighborhood k.val
  trivialization k := CircleFibration.restrictLocalChart F A hK (F.neighborhood k.val)
    (F.trivialization k.val) (F.projection_trivialization k.val)
  projection_trivialization _ _ := rfl

theorem CircleFibration.restrict_projection_val
    (z : ↥(⊤ : TopologicalSpace.Opens (CircleFibration.restrictTotal F A hK).Carrier)) :
    ((CircleFibration.restrict F A hK).projection z).val = F.projection z.val.val :=
  rfl

theorem CircleFibration.restrict_trivialization_snd
    (k : (CircleFibration.restrict F A hK).base.Carrier)
    (z : TopologicalSpace.Opens.comap (CircleFibration.restrict F A hK).projection
      ((CircleFibration.restrict F A hK).neighborhood k)) :
    ((CircleFibration.restrict F A hK).trivialization k z).2 =
      (F.trivialization k.val ⟨z.val.val.val, z.2⟩).2 :=
  rfl

def PrincipalAtlas.restrict (PA : PrincipalAtlas F) :
    PrincipalAtlas (CircleFibration.restrict F A hK) where
  count := PA.count
  domain i := CircleFibration.restrictOpen F A hK (PA.domain i)
  covers y := PA.covers y.val
  chart i := CircleFibration.restrictLocalChart F A hK (PA.domain i) (PA.chart i) (PA.chart_fst i)
  chart_fst _ _ := rfl
  transition i j y := PA.transition i j y.val
  chart_snd i j x hi hj := PA.chart_snd i j x.val.val hi hj

theorem CircleFibration.restrict_isGloballyTrivial (PA : PrincipalAtlas F) (P : PlanarBase.{u} 1)
    (e : (CircleFibration.restrictBase F A hK).Carrier ≃ₘ⟮SurfaceModel.model
      (CircleFibration.restrictBase F A hK).kind, SurfaceModel.model P.surface.kind⟯
      P.surface.Carrier) :
    CircleFibration.IsGloballyTrivial (CircleFibration.restrict F A hK) :=
  (PrincipalAtlas.restrict F A hK PA).isGloballyTrivial_of_planarBase P e

theorem CircleFibration.restrict_isGloballyTrivial_of_subset (k : K)
    (hk : K ⊆ F.neighborhood k.val) :
    CircleFibration.IsGloballyTrivial (CircleFibration.restrict F A hK) :=
  CircleFibration.isGloballyTrivial_of_forall_mem (CircleFibration.restrict F A hK) k
    fun y => hk y.2

end Restrict

end GC.Seifert
