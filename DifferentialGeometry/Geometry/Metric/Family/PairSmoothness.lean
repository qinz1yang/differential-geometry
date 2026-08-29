import DifferentialGeometry.Geometry.Metric.Family.Basic
import DifferentialGeometry.Bundle.Equiv
import DifferentialGeometry.Bundle.LocalFrameRegularity
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.Geometry.Curvature

open Bundle
open scoped Manifold ContDiff Topology BigOperators

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

namespace MetricFamilySmoothOn

omit [CompleteSpace E] in
private lemma metricCoord_eq_sum
    (g : SmoothRiemannianMetric I M) (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet)
    (v w : E) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[Real] Real)
        (fun y : M => TangentSpace I y →L[Real] Real) x₀ x x₀ x (g.inner x) v w =
      ∑ i, ∑ j,
        ((Module.finBasis Real E).repr v) i * ((Module.finBasis Real E).repr w) j *
          g.inner x
            ((trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame
              (Module.finBasis Real E) i x)
            ((trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame
              (Module.finBasis Real E) j x) := by
  classical
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  let b := Module.finBasis Real E
  have hxR : x ∈ (trivializationAt Real (Bundle.Trivial M Real) x₀).baseSet :=
    Set.mem_univ x
  rw [inCoordinates_apply_eq₂ (𝕜 := Real)
    (F₁ := E) (F₂ := E) (F₃ := Real)
    (E₁ := TangentSpace I) (E₂ := TangentSpace I)
    (E₃ := Bundle.Trivial M Real)
    (x₀ := x₀) (x := x) (ϕ := g.inner x) (v := v) (w := w) hx hx hxR]
  rw [(trivializationAt Real (Bundle.Trivial M Real) x₀).coe_linearMapAt_of_mem hxR]
  simp only [Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.trivialization_apply]
  rw [← Bundle.Trivialization.symmL_apply (R := Real)
      (trivializationAt E (TangentSpace I : M → Type _) x₀) hx v,
    ← Bundle.Trivialization.symmL_apply (R := Real)
      (trivializationAt E (TangentSpace I : M → Type _) x₀) hx w]
  change g.inner x (e.symmL Real x v) (e.symmL Real x w) = _
  have hvdec : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
  have hwdec : w = ∑ j, b.repr w j • b j := (b.sum_repr w).symm
  have hsymm_v : e.symmL Real x v = ∑ i, b.repr v i • e.localFrame b i x := by
    conv_lhs => rw [hvdec]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    congr 1
    rw [e.localFrame_apply_of_mem_baseSet (b := b) hx]
    exact Bundle.Trivialization.symmL_apply e hx (b i)
  have hsymm_w : e.symmL Real x w = ∑ j, b.repr w j • e.localFrame b j x := by
    conv_lhs => rw [hwdec]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul]
    congr 1
    rw [e.localFrame_apply_of_mem_baseSet (b := b) hx]
    exact Bundle.Trivialization.symmL_apply e hx (b j)
  rw [hsymm_v, hsymm_w]
  have hleft :
      g.inner x (∑ i, b.repr v i • e.localFrame b i x) =
        ∑ i, b.repr v i • g.inner x (e.localFrame b i x) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
  rw [hleft, sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_apply, smul_eq_mul]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul]
  ring

omit [CompleteSpace E] in
theorem metricCLMSmoothAt
    {D : RealTimeInterval}
    {g_fam : Real → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {t : Real} {x : M} (hDreg : D.regular ∈ 𝓝 t) :
    ContMDiffAt (𝓘(Real, Real).prod I)
      (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
      (fun q : Real × M =>
        TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun y => TangentSpace I y →L[Real]
            TangentSpace I y →L[Real] Real)
          q.2 ((g_fam q.1).inner q.2))
      (t, x) := by
  classical
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  let b := Module.finBasis Real E
  have hxe : x ∈ e.baseSet := by
    simp [e]
  have hframe :
      IsLocalFrameOn I E ∞ (e.localFrame b) e.baseSet :=
    e.isLocalFrameOn_localFrame_baseSet I ∞ b
  have hcompOn := hG.frameCompSmooth (e.localFrame b) hframe
  have hmemProd : (D.regular ×ˢ e.baseSet : Set (Real × M)) ∈ 𝓝 (t, x) :=
    prod_mem_nhds hDreg (e.open_baseSet.mem_nhds hxe)
  have hcompAt : ∀ i j,
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun q : Real × M =>
          (g_fam q.1).inner q.2
            (e.localFrame b i q.2) (e.localFrame b j q.2))
        (t, x) := fun i j =>
    (hcompOn i j).contMDiffAt hmemProd
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_snd, ?_⟩
  apply contMDiffAt_clm_of_pointwise (IB := 𝓘(Real, Real).prod I) (X := Real × M)
  intro v
  apply contMDiffAt_clm_of_pointwise (IB := 𝓘(Real, Real).prod I) (X := Real × M)
  intro w
  have hsum : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun q : Real × M =>
        ∑ i, ∑ j, b.repr v i * b.repr w j *
          (g_fam q.1).inner q.2
            (e.localFrame b i q.2) (e.localFrame b j q.2))
      (t, x) := by
    refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
    exact (contMDiffAt_const (c := b.repr v i * b.repr w j)).mul (hcompAt i j)
  refine hsum.congr_of_eventuallyEq ?_
  have hbase : ∀ᶠ q : Real × M in 𝓝 (t, x), q.2 ∈ e.baseSet :=
    (continuous_snd.tendsto (t, x)).eventually (e.open_baseSet.mem_nhds hxe)
  filter_upwards [hbase] with q hq
  change ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[Real] Real)
      (fun y : M => TangentSpace I y →L[Real] Real)
      x q.2 x q.2 ((g_fam q.1).inner q.2) v w = _
  simpa only [e, b] using
    metricCoord_eq_sum (I := I) (g_fam q.1) x hq v w

omit [CompleteSpace E] in
theorem pairSmoothAt
    {D : RealTimeInterval}
    {g_fam : ℝ → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {t : Real} {x : M} (hDreg : D.regular ∈ 𝓝 t)
    (V : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _)) :
    ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun q : Real × M =>
        (g_fam q.1).inner q.2 ((V 0) q.2) ((V 1) q.2))
      (t, x) := by
  classical
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  let b := Module.finBasis Real E
  have hxe : x ∈ e.baseSet := by
    simp [e]
  have hframe :
      IsLocalFrameOn I E (∞ : WithTop ℕ∞) (e.localFrame b) e.baseSet :=
    e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) b
  have hcompOn := hG.frameCompSmooth (e.localFrame b) hframe
  have hmemProd : (D.regular ×ˢ e.baseSet : Set (Real × M)) ∈ 𝓝 (t, x) :=
    prod_mem_nhds hDreg (e.open_baseSet.mem_nhds hxe)
  have hcompAt : ∀ i j,
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real)
        (∞ : WithTop ℕ∞)
        (fun q : Real × M =>
          (g_fam q.1).inner q.2
            (e.localFrame b i q.2) (e.localFrame b j q.2))
        (t, x) := fun i j =>
    (hcompOn i j).contMDiffAt hmemProd
  have hcoeff : ∀ (a : Fin 2) i,
      ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M => e.localFrameCoeff I b i y ((V a) y)) x := fun a i =>
    contMDiffAt_localFrameCoeff (I := I) b hxe
      ((V a).contMDiff.contMDiffAt) i
  have hsum :
      ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real)
        (∞ : WithTop ℕ∞)
        (fun q : Real × M =>
          ∑ i, ∑ j,
            e.localFrameCoeff I b i q.2 ((V 0) q.2) *
              e.localFrameCoeff I b j q.2 ((V 1) q.2) *
              (g_fam q.1).inner q.2
                (e.localFrame b i q.2) (e.localFrame b j q.2))
        (t, x) := by
    refine ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ => ?_
    exact (((hcoeff 0 i).comp (t, x) contMDiffAt_snd).mul
      ((hcoeff 1 j).comp (t, x) contMDiffAt_snd)).mul (hcompAt i j)
  refine hsum.congr_of_eventuallyEq ?_
  have hev0 := e.eventually_eq_localFrame_sum_coeff_smul
    (I := I) b (s := fun y => (V 0) y) hxe
  have hev1 := e.eventually_eq_localFrame_sum_coeff_smul
    (I := I) b (s := fun y => (V 1) y) hxe
  have hev : ∀ᶠ q : Real × M in 𝓝 (t, x),
      ((V 0) q.2 =
        ∑ i, e.localFrameCoeff I b i q.2 ((V 0) q.2) • e.localFrame b i q.2) ∧
      ((V 1) q.2 =
        ∑ i, e.localFrameCoeff I b i q.2 ((V 1) q.2) • e.localFrame b i q.2) :=
    (continuous_snd.tendsto (t, x)).eventually (hev0.and hev1)
  filter_upwards [hev] with q hq
  have hexp :
      (g_fam q.1).inner q.2 ((V 0) q.2) ((V 1) q.2) =
        (g_fam q.1).inner q.2
          (∑ i, e.localFrameCoeff I b i q.2 ((V 0) q.2) • e.localFrame b i q.2)
          (∑ j, e.localFrameCoeff I b j q.2 ((V 1) q.2) • e.localFrame b j q.2) := by
    rw [← hq.1, ← hq.2]
  rw [hexp]
  simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
    smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    ring

end MetricFamilySmoothOn
end DifferentialGeometry.Geometry.Curvature

end
