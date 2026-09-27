import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.AdaptedField.InnerProduct
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.AdaptedField.Defs
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.PullbackLocalIso
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross

noncomputable section
open Set Filter Bundle Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]
  {D D' : RealTimeInterval}

theorem IsLAdaptedAt.comp_of_localPullMetric
    (S : SolutionOn (I := I) (M := M) D)
    (Q : SolutionOn (I := J) (M := N) D')
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f)
    (T : ℝ) (α : ℝ → M) (P : ∀ r, TangentSpace I (α r)) {s : ℝ}
    (hmetric : S.base.metric (T - s ^ 2) = localPullMetric (Q.base.metric (T - s ^ 2)) f hf)
    (hα : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ α s)
    (hP : DifferentiableAt ℝ (chartRepAt (I := I) α P s) s)
    (h : IsLAdaptedAt S T α P s) :
    IsLAdaptedAt Q T (f ∘ α) (fun r => mfderiv I J f (α r) (P r)) s := by
  let g := S.base.metric (T - s ^ 2)
  let g' := Q.base.metric (T - s ^ 2)
  have hm (x : M) (_ : x ∈ (univ : Set M)) (v w : TangentSpace I x) :
      g.inner x v w = g'.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) := by
    rw [show g = localPullMetric g' f hf from hmetric, localPullMetric_inner]
  have hnat := covDerivAlong_map_of_local_isometry_on g g' isOpen_univ
    (fun x => hf x.val) hm α P (mem_univ _) hα hP
  change mfderiv I J f (α s) (covDerivAlong (S.base.metric (T - s ^ 2)) α P s) =
    covDerivAlong (Q.base.metric (T - s ^ 2)) (f ∘ α)
      (fun r => mfderiv I J f (α r) (P r)) s at hnat
  unfold IsLAdaptedAt at h ⊢
  rw [← hnat, h, map_smul]
  congr 1
  rw [hmetric]
  exact ricciSharp_localPull g' f hf (α s) (P s)

theorem IsLAdapted.comp_of_localPullMetric
    (S : SolutionOn (I := I) (M := M) D)
    (Q : SolutionOn (I := J) (M := N) D')
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f)
    (T : ℝ) (α : ℝ → M) (P : ∀ r, TangentSpace I (α r)) {K : Set ℝ}
    (hmetric : ∀ s ∈ K, S.base.metric (T - s ^ 2) = localPullMetric (Q.base.metric (T - s ^ 2)) f hf)
    (hα : ∀ s ∈ K, ContMDiffAt 𝓘(ℝ, ℝ) I ∞ α s)
    (hP : ∀ s ∈ K, DifferentiableAt ℝ (chartRepAt (I := I) α P s) s)
    (h : IsLAdapted S T α P K) :
    IsLAdapted Q T (f ∘ α) (fun r => mfderiv I J f (α r) (P r)) K := by
  intro s hs
  exact (h s hs).comp_of_localPullMetric S Q f hf T α P (hmetric s hs) (hα s hs) (hP s hs)

theorem IsLAdapted.eqOn_map_of_localPullMetric
    (S : SolutionOn (I := I) (M := M) D)
    (Q : SolutionOn (I := J) (M := N) D') (hQ : IsSolutionOn Q)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f)
    (T : ℝ) (α : ℝ → M) (P : ∀ r, TangentSpace I (α r))
    (R : ∀ r, TangentSpace J (f (α r))) {K : Set ℝ}
    (hK : IsOpen K) (hconn : IsPreconnected K) {s₀ : ℝ} (hs₀ : s₀ ∈ K)
    (hreg : ∀ r ∈ K, T - r ^ 2 ∈ D'.regular)
    (hP : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun r => (TotalSpace.mk' E (α r) (P r) : TangentBundle I M)) K)
    (hR : ∀ r ∈ K, DifferentiableAt ℝ (chartRepAt (I := J) (f ∘ α) R r) r)
    (hmetric : ∀ r ∈ K,
      S.base.metric (T - r ^ 2) = localPullMetric (Q.base.metric (T - r ^ 2)) f hf)
    (hDP : IsLAdapted S T α P K) (hDR : IsLAdapted Q T (f ∘ α) R K)
    (heq : mfderiv I J f (α s₀) (P s₀) = R s₀) :
    ∀ r ∈ K, mfderiv I J f (α r) (P r) = R r := by
  have hα : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ α K :=
    (contMDiff_proj (TangentSpace I)).comp_contMDiffOn hP
  let Pf : ∀ r, TangentSpace J (f (α r)) := fun r => mfderiv I J f (α r) (P r)
  have hPdiff (r : ℝ) (hr : r ∈ K) :
      DifferentiableAt ℝ (chartRepAt (I := I) α P r) r :=
    differentiableAt_chartRepAt_of_contMDiffAt_two
      ((hP r hr).contMDiffAt (hK.mem_nhds hr) |>.of_le (WithTop.coe_le_coe.mpr le_top))
  have hαAt (r : ℝ) (hr : r ∈ K) : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ α r :=
    (hα r hr).contMDiffAt (hK.mem_nhds hr)
  have hPf : ContMDiffOn 𝓘(ℝ, ℝ) J.tangent ∞
      (fun r => (TotalSpace.mk' F (f (α r)) (Pf r) : TangentBundle J N)) K := by
    exact (hf.contMDiff.contMDiff_tangentMap (m := ∞) le_rfl).comp_contMDiffOn hP
  have hPfdiff (r : ℝ) (hr : r ∈ K) :
      DifferentiableAt ℝ (chartRepAt (I := J) (f ∘ α) Pf r) r :=
    differentiableAt_chartRepAt_of_contMDiffAt_two
      ((hPf r hr).contMDiffAt (hK.mem_nhds hr) |>.of_le (WithTop.coe_le_coe.mpr le_top))
  have hDPf : IsLAdapted Q T (f ∘ α) Pf K :=
    hDP.comp_of_localPullMetric S Q f hf T α P hmetric hαAt hPdiff
  exact hDPf.eqOn_of_eq_at Q hQ T (f ∘ α) Pf R hconn hs₀ hreg
    (fun r hr => ((hf.contMDiff.contMDiffAt).comp r (hαAt r hr)).mdifferentiableAt (by simp))
    hPfdiff hR hDR heq

theorem IsLAdapted.eqOn_tangentMap_of_curve_eqOn
    (S : SolutionOn (I := I) (M := M) D) (Q : SolutionOn (I := J) (M := N) D') (hQ : IsSolutionOn Q)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f) (T : ℝ)
    (α : ℝ → M) (β : ℝ → N) (P : ∀ r, TangentSpace I (α r)) (R : ∀ r, TangentSpace J (β r))
    {K : Set ℝ} (hK : IsOpen K) (hconn : IsPreconnected K) {s₀ : ℝ} (hs₀ : s₀ ∈ K)
    (hreg : ∀ r ∈ K, T - r ^ 2 ∈ D'.regular)
    (hP : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞ (fun r => (TotalSpace.mk' E (α r) (P r) : TangentBundle I M)) K)
    (hR : ∀ r ∈ K, DifferentiableAt ℝ (chartRepAt (I := J) β R r) r)
    (hmetric : ∀ r ∈ K, S.base.metric (T - r ^ 2) = localPullMetric (Q.base.metric (T - r ^ 2)) f hf)
    (hDP : IsLAdapted S T α P K) (hDR : IsLAdapted Q T β R K)
    (heqcurve : EqOn β (f ∘ α) K)
    (heq : (TotalSpace.mk' F (f (α s₀)) (mfderiv I J f (α s₀) (P s₀)) : TangentBundle J N) =
      TotalSpace.mk' F (β s₀) (R s₀)) :
    EqOn (fun r => (TotalSpace.mk' F (f (α r)) (mfderiv I J f (α r) (P r)) : TangentBundle J N))
      (fun r => (TotalSpace.mk' F (β r) (R r) : TangentBundle J N)) K := by
  let Rf : ∀ r, TangentSpace J (f (α r)) := fun r => (R r : F)
  have hcurvegerm (r : ℝ) (hr : r ∈ K) : (f ∘ α) =ᶠ[𝓝 r] β := by
    filter_upwards [hK.mem_nhds hr] with t ht
    exact (heqcurve ht).symm
  have hRdiff (r : ℝ) (hr : r ∈ K) :
      DifferentiableAt ℝ (chartRepAt (I := J) (f ∘ α) Rf r) r := by
    have hrep := DifferentialGeometry.Geometry.Riemannian.chartRep_congr_curve
      (I := J) Rf R (hcurvegerm r hr) (Filter.Eventually.of_forall fun _ => rfl)
    exact (hR r hr).congr_of_eventuallyEq hrep
  have hDRf : IsLAdapted Q T (f ∘ α) Rf K := by
    intro r hr
    have hcov := DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
      (I := J) (Q.base.metric (T - r ^ 2)) Rf R (hcurvegerm r hr)
      (Filter.Eventually.of_forall fun _ => rfl)
    have h := hDR r hr
    change (covDerivAlong (I := J) (Q.base.metric (T - r ^ 2)) (f ∘ α) Rf r : F) = _
    change (covDerivAlong (I := J) (Q.base.metric (T - r ^ 2)) (f ∘ α) Rf r : F) =
      (covDerivAlong (I := J) (Q.base.metric (T - r ^ 2)) β R r : F) at hcov
    rw [hcov, h]
    change (-2 * r) • (ricciSharp (I := J) (Q.base.metric (T - r ^ 2)) (β r) (R r) : F) =
      (-2 * r) • (ricciSharp (I := J) (Q.base.metric (T - r ^ 2)) (f (α r)) (R r) : F)
    rw [heqcurve hr]
    rfl
  have heqv : mfderiv I J f (α s₀) (P s₀) = Rf s₀ :=
    congrArg (fun z : TangentBundle J N => (z.2 : F)) heq
  have heqfield := IsLAdapted.eqOn_map_of_localPullMetric S Q hQ f hf T α P Rf hK hconn hs₀ hreg
    hP hRdiff hmetric hDP hDRf heqv
  intro r hr
  have hbase := heqcurve hr
  have hfield := heqfield r hr
  change (TotalSpace.mk' F (f (α r)) ((mfderiv I J f (α r) (P r)) : F) : TangentBundle J N) = _
  apply Bundle.TotalSpace.ext hbase.symm
  exact heq_of_eq hfield

theorem IsLAdapted.eventuallyEq_tangentMap_of_curve_eventuallyEq
    (S : SolutionOn (I := I) (M := M) D)
    (Q : SolutionOn (I := J) (M := N) D') (hQ : IsSolutionOn Q)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f)
    (T : ℝ) (α : ℝ → M) (β : ℝ → N)
    (P : ∀ r, TangentSpace I (α r)) (R : ∀ r, TangentSpace J (β r))
    {K : Set ℝ} {s₀ : ℝ} (hK : K ∈ 𝓝 s₀)
    (hreg : ∀ r ∈ K, T - r ^ 2 ∈ D'.regular)
    (hP : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun r => (TotalSpace.mk' E (α r) (P r) : TangentBundle I M)) K)
    (hR : ∀ r ∈ K, DifferentiableAt ℝ (chartRepAt (I := J) β R r) r)
    (hmetric : ∀ r ∈ K,
      S.base.metric (T - r ^ 2) = localPullMetric (Q.base.metric (T - r ^ 2)) f hf)
    (hDP : IsLAdapted S T α P K) (hDR : IsLAdapted Q T β R K)
    (heqcurve : β =ᶠ[𝓝 s₀] f ∘ α)
    (heq : (TotalSpace.mk' F (f (α s₀)) (mfderiv I J f (α s₀) (P s₀)) : TangentBundle J N) =
      TotalSpace.mk' F (β s₀) (R s₀)) :
    (fun r => (TotalSpace.mk' F (f (α r)) (mfderiv I J f (α r) (P r)) : TangentBundle J N)) =ᶠ[𝓝 s₀]
      (fun r => (TotalSpace.mk' F (β r) (R r) : TangentBundle J N)) := by
  obtain ⟨a, b, hs, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (inter_mem hK heqcurve)
  have hsubK : Ioo a b ⊆ K := fun _ hr => (hsub hr).1
  have hh := IsLAdapted.eqOn_tangentMap_of_curve_eqOn S Q hQ f hf T α β P R
    isOpen_Ioo isPreconnected_Ioo hs (fun r hr => hreg r (hsubK hr))
    (hP.mono hsubK) (fun r hr => hR r (hsubK hr)) (fun r hr => hmetric r (hsubK hr))
    (fun r hr => hDP r (hsubK hr)) (fun r hr => hDR r (hsubK hr))
    (fun {r} hr => (hsub hr).2) heq
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
  exact hh hr

end DifferentialGeometry.PDE.RicciFlow.Perelman
end
