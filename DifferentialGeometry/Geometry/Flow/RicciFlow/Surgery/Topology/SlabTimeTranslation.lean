import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.IntervalTransport
import Mathlib.Tactic.Linarith

set_option autoImplicit false

noncomputable section

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

universe u
variable {P : OrientedThreeStage.{u}}

private local instance : IsManifold ThreeModel 1 P.Carrier :=
  IsManifold.of_le (I := ThreeModel) (M := P.Carrier) (n := ∞) (by decide)

theorem MetricSmoothUpTo.timeTranslate {g : ℝ → P.Metric} {J J' : Set ℝ}
    (hg : P.MetricSmoothUpTo g J) (a : ℝ)
    (hJ : MapsTo (fun t => t - a) J' J) :
    P.MetricSmoothUpTo (fun t => g (t - a)) J' := by
  intro p t ht
  obtain ⟨U, hU, hp, hUb, V, hV, htV, A, hA, hEq⟩ := hg p (t - a) (hJ ht)
  refine ⟨U, hU, hp, hUb, (fun s : ℝ => s - a) ⁻¹' V,
    hV.preimage (continuous_id.sub continuous_const), htV,
    (fun z i j => A (z.1 - a, z.2) i j), ?_, ?_⟩
  · intro i j
    have hmap : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) (𝓘(ℝ, ℝ).prod ThreeModel) ∞
        (fun z : ℝ × P.Carrier => (z.1 - a, z.2)) :=
      (contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd
    exact (hA i j).comp hmap.contMDiffOn (fun z hz => ⟨hz.1, hz.2⟩)
  · intro s hs x hx i j
    exact hEq (s - a) ⟨hs.1, hJ hs.2⟩ x hx i j

private def translatedFlow {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D)
    (a : ℝ) (D' : RealTimeInterval) :
    SolutionOn (I := ThreeModel) (M := P.Carrier) D' :=
  (S.timeShift (-a)).cast D'

private theorem translatedFlow_metric_eq {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D)
    (a : ℝ) (D' : RealTimeInterval) :
    (translatedFlow S a D').base.metric = fun t => S.base.metric (t - a) := rfl

private theorem translatedFlow_equation {D D' : RealTimeInterval}
    {S : SolutionOn (I := ThreeModel) (M := P.Carrier) D}
    (hS : IsSolutionOn S) (a : ℝ)
    (hcarrier : D'.carrier = {t | t - a ∈ D.carrier})
    (hregular : D'.regular = {t | t - a ∈ D.regular}) :
    IsSolutionOn (translatedFlow S a D') := by
  apply isSolutionOn_cast (isSolutionOn_timeShift hS (-a))
  · rw [hcarrier]
    ext t
    simp only [RealTimeInterval.timeShift_carrier, mem_ofPred_eq, sub_eq_add_neg]
  · rw [hregular]
    ext t
    simp only [RealTimeInterval.timeShift_regular, mem_ofPred_eq, sub_eq_add_neg]

private theorem preimage_Ico_translate (s e a : ℝ) :
    Ico (s + a) (e + a) = {t | t - a ∈ Ico s e} := by
  ext t
  simp only [mem_Ico, mem_ofPred_eq]
  constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]

private theorem preimage_Ioo_translate (s e a : ℝ) :
    Ioo (s + a) (e + a) = {t | t - a ∈ Ioo s e} := by
  ext t
  simp only [mem_Ioo, mem_ofPred_eq]
  constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]

private theorem preimage_Icc_translate (s e a : ℝ) :
    Icc (s + a) (e + a) = {t | t - a ∈ Icc s e} := by
  ext t
  simp only [mem_Icc, mem_ofPred_eq]
  constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]

def IncomingSlab.timeTranslate {s e : ℝ} (G : P.IncomingSlab s e) (a : ℝ) :
    P.IncomingSlab (s + a) (e + a) where
  lt := add_lt_add_left G.lt a
  flow := translatedFlow G.flow a _
  equation := translatedFlow_equation G.equation a
    (preimage_Ico_translate s e a) (preimage_Ioo_translate s e a)
  smoothUpTo := by
    simpa only [translatedFlow_metric_eq] using G.smoothUpTo.timeTranslate a
      (show MapsTo (fun t => t - a) (Ico (s + a) (e + a)) (Ico s e) from
        fun t ht => by rwa [preimage_Ico_translate s e a] at ht)

def ClosedSlab.timeTranslate {s e : ℝ} (G : P.ClosedSlab s e) (a : ℝ) :
    P.ClosedSlab (s + a) (e + a) where
  lt := add_lt_add_left G.lt a
  flow := translatedFlow G.flow a _
  equation := translatedFlow_equation G.equation a
    (preimage_Icc_translate s e a) (preimage_Ioo_translate s e a)
  smoothUpTo := by
    simpa only [translatedFlow_metric_eq] using G.smoothUpTo.timeTranslate a
      (show MapsTo (fun t => t - a) (Icc (s + a) (e + a)) (Icc s e) from
        fun t ht => by rwa [preimage_Icc_translate s e a] at ht)

@[simp] theorem IncomingSlab.timeTranslate_metric {s e : ℝ}
    (G : P.IncomingSlab s e) (a t : ℝ) :
    (G.timeTranslate a).flow.base.metric t = G.flow.base.metric (t - a) := rfl

@[simp] theorem ClosedSlab.timeTranslate_metric {s e : ℝ}
    (G : P.ClosedSlab s e) (a t : ℝ) :
    (G.timeTranslate a).flow.base.metric t = G.flow.base.metric (t - a) := rfl

theorem IncomingSlab.timeTranslate_metric_add {s e : ℝ}
    (G : P.IncomingSlab s e) (a t : ℝ) :
    (G.timeTranslate a).flow.base.metric (t + a) = G.flow.base.metric t := by
  rw [timeTranslate_metric, add_sub_cancel_right]

theorem ClosedSlab.timeTranslate_metric_add {s e : ℝ}
    (G : P.ClosedSlab s e) (a t : ℝ) :
    (G.timeTranslate a).flow.base.metric (t + a) = G.flow.base.metric t := by
  rw [timeTranslate_metric, add_sub_cancel_right]

theorem IncomingSlab.timeTranslate_initial_metric {s e : ℝ}
    (G : P.IncomingSlab s e) (a : ℝ) :
    (G.timeTranslate a).flow.base.metric (s + a) = G.flow.base.metric s :=
  G.timeTranslate_metric_add a s

theorem ClosedSlab.timeTranslate_initial_metric {s e : ℝ}
    (G : P.ClosedSlab s e) (a : ℝ) :
    (G.timeTranslate a).flow.base.metric (s + a) = G.flow.base.metric s :=
  G.timeTranslate_metric_add a s

@[simp] theorem IncomingSlab.timeTranslate_riemannNorm {s e : ℝ}
    (G : P.IncomingSlab s e) (a t : ℝ) (x : P.Carrier) :
    (G.timeTranslate a).riemannNorm t x = G.riemannNorm (t - a) x := rfl

theorem IncomingSlab.timeTranslate_singularEndpoint_iff {s e : ℝ}
    (G : P.IncomingSlab s e) (a : ℝ) :
    (G.timeTranslate a).SingularEndpoint ↔ G.SingularEndpoint := by
  constructor
  · intro h L hL d hd
    have hd' : d + a ∈ Ico (s + a) (e + a) :=
      ⟨add_le_add_left hd.1 a, add_lt_add_left hd.2 a⟩
    obtain ⟨t, ht, x, hx⟩ := h L hL (d + a) hd'
    refine ⟨t - a, ⟨?_, ?_⟩, x, ?_⟩
    · linarith [ht.1]
    · linarith [ht.2]
    · simpa only [timeTranslate_riemannNorm] using hx
  · intro h L hL d hd
    have hd' : d - a ∈ Ico s e := by
      constructor <;> linarith [hd.1, hd.2]
    obtain ⟨t, ht, x, hx⟩ := h L hL (d - a) hd'
    refine ⟨t + a, ⟨?_, ?_⟩, x, ?_⟩
    · linarith [ht.1]
    · linarith [ht.2]
    · simpa only [timeTranslate_riemannNorm, add_sub_cancel_right] using hx

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage
