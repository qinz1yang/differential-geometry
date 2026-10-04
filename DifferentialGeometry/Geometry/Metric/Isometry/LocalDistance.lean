import DifferentialGeometry.Geometry.Metric.Comparison.DerivativeDistance
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

noncomputable section
open Bundle Filter Manifold Set
open scoped ContDiff Topology ENNReal NNReal
namespace DifferentialGeometry.Geometry.Metric

private theorem exists_real_closedEBall_subset {X : Type*} [PseudoEMetricSpace X]
    {U : Set X} {x : X} (hU : U ∈ 𝓝 x) :
    ∃ R : ℝ, 0 < R ∧ Metric.closedEBall x (ENNReal.ofReal R) ⊆ U := by
  obtain ⟨r, hr, hsub⟩ := EMetric.mem_nhds_iff.mp hU
  obtain ⟨s, hs, hsr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
  refine ⟨s, by exact_mod_cast hs, ?_⟩
  intro y hy
  apply hsub
  exact lt_of_le_of_lt (by simpa using hy) hsr

private theorem centered_buffer {X : Type*} [PseudoEMetricSpace X]
    {p x y : X} {R : ℝ} (hR : 0 < R)
    (hx : x ∈ Metric.eball p (ENNReal.ofReal (R / 3)))
    (hy : y ∈ Metric.eball p (ENNReal.ofReal (R / 3))) :
    Metric.closedEBall x (ENNReal.ofReal (2*R/3)) ⊆ Metric.closedEBall p (ENNReal.ofReal R) ∧
      edist x y < ENNReal.ofReal (2*R/3) := by
  have hx' : edist x p < ENNReal.ofReal (R/3) := hx
  have hy' : edist p y < ENNReal.ofReal (R/3) := by simpa [edist_comm] using hy
  constructor
  · intro z hz
    calc
      edist z p ≤ edist z x + edist x p := edist_triangle _ _ _
      _ ≤ ENNReal.ofReal (2*R/3) + ENNReal.ofReal (R/3) := add_le_add hz hx'.le
      _ = ENNReal.ofReal R := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  · calc
      edist x y ≤ edist x p + edist p y := edist_triangle _ _ _
      _ < ENNReal.ofReal (R/3) + ENNReal.ofReal (R/3) := ENNReal.add_lt_add hx' hy'
      _ = ENNReal.ofReal (2*R/3) := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

section
variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [PseudoEMetricSpace M] [ChartedSpace H M]
  [PseudoEMetricSpace N] [ChartedSpace H' N]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [RiemannianBundle (TangentSpace J : N → Type _)]
  [IsRiemannianManifold I M] [IsRiemannianManifold J N]

private theorem local_nonexpanding {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I J 1 f U)
    (hspeed : ∀ z ∈ U, ∀ v : TangentSpace I z, ‖mfderiv I J f z v‖ₑ ≤ ‖v‖ₑ)
    {p : M} (hp : p ∈ U) :
    ∃ V : Set M, V ∈ 𝓝 p ∧ V ⊆ U ∧ LipschitzOnWith 1 f V := by
  obtain ⟨R, hR, hsub⟩ := exists_real_closedEBall_subset (hU.mem_nhds hp)
  refine ⟨Metric.eball p (ENNReal.ofReal (R/3)), Metric.eball_mem_nhds _ (by positivity), ?_, ?_⟩
  · intro z hz
    apply hsub
    exact hz.le.trans (ENNReal.ofReal_le_ofReal (by linarith))
  · intro x hx y hy
    obtain ⟨hbuf, hxy⟩ := centered_buffer hR hx hy
    simpa only [ENNReal.coe_one, one_mul] using
      Manifold.edist_map_le_mul_of_enorm_mfderiv_le_on_closedEBall
        hU hf (hbuf.trans hsub)
        (C := 1) (fun z hz v => by simpa using hspeed z (hsub (hbuf hz)) v) hxy

private theorem exists_isometry_nhds_of_mfderiv_norm
    (Φ : OpenPartialHomeomorph M N)
    (hΦ : ContMDiffOn I J 1 Φ Φ.source)
    (hΦinv : ContMDiffOn J I 1 Φ.symm Φ.target)
    (hiso : ∀ x ∈ Φ.source, ∀ v : TangentSpace I x,
      ‖mfderiv I J Φ x v‖ₑ = ‖v‖ₑ)
    {p : M} (hp : p ∈ Φ.source) :
    ∃ V : Set M, V ∈ 𝓝 p ∧ V ⊆ Φ.source ∧ Isometry (fun x : V => Φ (x : M)) := by
  have hinv : ∀ y ∈ Φ.target, ∀ w : TangentSpace J y,
      ‖mfderiv J I Φ.symm y w‖ₑ ≤ ‖w‖ₑ := by
    intro y hy w
    have hd : Φ.MDifferentiable I J :=
      ⟨hΦ.mdifferentiableOn one_ne_zero, hΦinv.mdifferentiableOn one_ne_zero⟩
    have hcomp := DFunLike.congr_fun (hd.comp_symm_deriv hy) w
    have he := hiso (Φ.symm y) (Φ.map_target hy) (mfderiv J I Φ.symm y w)
    change ‖mfderiv I J Φ (Φ.symm y) (mfderiv J I Φ.symm y w)‖ₑ = _ at he
    change mfderiv I J Φ (Φ.symm y) (mfderiv J I Φ.symm y w) = w at hcomp
    rw [hcomp] at he
    erw [Φ.right_inv hy] at he
    exact he.ge
  obtain ⟨U, hU, hUsub, hforw⟩ := local_nonexpanding Φ.open_source hΦ
    (fun x hx v => (hiso x hx v).le) hp
  obtain ⟨W, hW, hWsub, hback⟩ := local_nonexpanding Φ.open_target hΦinv hinv
    (Φ.map_source hp)
  have hcont : ContinuousAt Φ p := hΦ.continuousOn.continuousAt (Φ.open_source.mem_nhds hp)
  refine ⟨U ∩ Φ ⁻¹' W, inter_mem hU (hcont.preimage_mem_nhds hW), fun x hx => hUsub hx.1, ?_⟩
  intro x y
  change edist (Φ (x : M)) (Φ (y : M)) = edist (x : M) (y : M)
  apply le_antisymm
  · simpa using hforw x.2.1 y.2.1
  · have h := hback x.2.2 y.2.2
    erw [Φ.left_inv (hUsub x.2.1), Φ.left_inv (hUsub y.2.1)] at h
    simpa only [ENNReal.coe_one, one_mul] using h
end

section
variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [RegularSpace M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N] [RegularSpace N]

theorem exists_intrinsic_edist_eq_nhds_of_inner_eq {k l : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I k E (TangentSpace I : M → Type _))
    (h : ContMDiffRiemannianMetric J l F (TangentSpace J : N → Type _))
    (Φ : OpenPartialHomeomorph M N)
    (hΦ : ContMDiffOn I J 1 Φ Φ.source)
    (hΦinv : ContMDiffOn J I 1 Φ.symm Φ.target)
    (hinner : ∀ x ∈ Φ.source, ∀ v w : TangentSpace I x,
      h.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w) = g.inner x v w)
    {p : M} (hp : p ∈ Φ.source) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : RiemannianBundle (TangentSpace J : N → Type _) := ⟨h.toRiemannianMetric⟩
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ⊆ Φ.source ∧
      ∀ x ∈ V, ∀ y ∈ V, riemannianEDist J (Φ x) (Φ y) = riemannianEDist I x y := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace J : N → Type _) := ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : IsContinuousRiemannianBundle F (TangentSpace J : N → Type _) :=
    ⟨h.inner, h.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace N := PseudoEMetricSpace.ofRiemannianMetric J N
  have hn : ∀ x ∈ Φ.source, ∀ v : TangentSpace I x,
      ‖mfderiv I J Φ x v‖ₑ = ‖v‖ₑ := by
    intro x hx v
    rw [enorm_eq_iff_norm_eq, norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
    change Real.sqrt (h.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x v)) =
      Real.sqrt (g.inner x v v)
    rw [hinner x hx v v]
  obtain ⟨V, hV, hsub, hiso⟩ := exists_isometry_nhds_of_mfderiv_norm Φ hΦ hΦinv hn hp
  refine ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.mpr hV,
    interior_subset.trans hsub, fun x hx y hy => ?_⟩
  exact hiso.edist_eq ⟨x, interior_subset hx⟩ ⟨y, interior_subset hy⟩
end
end DifferentialGeometry.Geometry.Metric
