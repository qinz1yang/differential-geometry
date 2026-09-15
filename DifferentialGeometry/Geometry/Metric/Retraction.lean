import Mathlib.Analysis.InnerProductSpace.Dual
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Geometry.Metric.Product
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Topology.Manifold.OpenSubtype

noncomputable section

open scoped InnerProductSpace

namespace DifferentialGeometry.Geometry.Riemannian

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def retractionBilinearForm (G : E →L[ℝ] E →L[ℝ] ℝ)
    (R : F →L[ℝ] E) (J : E →L[ℝ] F) : F →L[ℝ] F →L[ℝ] ℝ :=
  G.bilinearComp R R + (show F →L[ℝ] F →L[ℝ] ℝ from innerSL ℝ).bilinearComp
    (ContinuousLinearMap.id ℝ F - J.comp R) (ContinuousLinearMap.id ℝ F - J.comp R)

theorem retractionBilinearForm_apply (G : E →L[ℝ] E →L[ℝ] ℝ)
    (R : F →L[ℝ] E) (J : E →L[ℝ] F) (v w : F) :
    retractionBilinearForm G R J v w = G (R v) (R w) + ⟪v - J (R v), w - J (R w)⟫_ℝ := rfl

theorem retractionBilinearForm_symm {G : E →L[ℝ] E →L[ℝ] ℝ}
    (hG : ∀ u v, G u v = G v u) (R : F →L[ℝ] E) (J : E →L[ℝ] F) (v w : F) :
    retractionBilinearForm G R J v w = retractionBilinearForm G R J w v := by
  rw [retractionBilinearForm_apply, retractionBilinearForm_apply, hG, real_inner_comm]

theorem retractionBilinearForm_pos {G : E →L[ℝ] E →L[ℝ] ℝ}
    (hG : ∀ u ≠ 0, 0 < G u u) (R : F →L[ℝ] E) (J : E →L[ℝ] F)
    {v : F} (hv : v ≠ 0) : 0 < retractionBilinearForm G R J v v := by
  rw [retractionBilinearForm_apply]
  by_cases hRv : R v = 0
  · simpa only [hRv, map_zero, sub_zero, zero_add] using real_inner_self_pos.mpr hv
  · exact add_pos_of_pos_of_nonneg (hG _ hRv) real_inner_self_nonneg

theorem retractionBilinearForm_map (G : E →L[ℝ] E →L[ℝ] ℝ)
    {R : F →L[ℝ] E} {J : E →L[ℝ] F} (hRJ : Function.LeftInverse R J) (u v : E) :
    retractionBilinearForm G R J (J u) (J v) = G u v := by
  simp only [retractionBilinearForm_apply, hRJ u, hRJ v, sub_self, inner_zero_left, add_zero]

theorem retractionBilinearForm_bilinearComp (G : E →L[ℝ] E →L[ℝ] ℝ)
    {R : F →L[ℝ] E} {J : E →L[ℝ] F} (hRJ : Function.LeftInverse R J) :
    (retractionBilinearForm G R J).bilinearComp J J = G := by
  ext u v
  exact retractionBilinearForm_map G hRJ u v

theorem retractionBilinearForm_eq_inner_of_mem_ker (G : E →L[ℝ] E →L[ℝ] ℝ)
    {R : F →L[ℝ] E} (J : E →L[ℝ] F) {v w : F} (hv : R v = 0) (hw : R w = 0) :
    retractionBilinearForm G R J v w = ⟪v, w⟫_ℝ := by
  simp only [retractionBilinearForm_apply, hv, hw, map_zero, sub_zero, zero_add]

theorem retractionBilinearForm_map_eq_zero_of_mem_ker
    (G : E →L[ℝ] E →L[ℝ] ℝ) {R : F →L[ℝ] E} {J : E →L[ℝ] F}
    (hRJ : Function.LeftInverse R J) (u : E) {w : F} (hw : R w = 0) :
    retractionBilinearForm G R J (J u) w = 0 := by
  simp only [retractionBilinearForm_apply, hRJ u, hw, map_zero, sub_self,
    inner_zero_left, add_zero]

end DifferentialGeometry.Geometry.Riemannian

noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

def retractionGraph (e : M → F) (r : F → M) (x : F) : M × F :=
  (r x, x - e (r x))

theorem contMDiff_retractionGraph
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {r : F → M} {U : TopologicalSpace.Opens F}
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r U) :
    ContMDiff 𝓘(ℝ, F) (I.prod 𝓘(ℝ, F)) ∞
      (fun x : U => retractionGraph e r x) := by
  have hR : ContMDiff 𝓘(ℝ, F) I ∞ (fun x : U => r x) :=
    hr.comp_contMDiff contMDiff_subtype_val (fun x => x.2)
  exact hR.prodMk (contMDiff_subtype_val.sub (he.comp hR))

theorem injective_mfderiv_retractionGraph
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {r : F → M} {U : TopologicalSpace.Opens F}
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r U) (x : U) :
    Function.Injective (mfderiv 𝓘(ℝ, F) (I.prod 𝓘(ℝ, F))
      (fun x : U => retractionGraph e r x) x) := by
  let p : M × F → F := fun y => e y.1 + y.2
  have hp : ContMDiff (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, F) ∞ p :=
    (he.comp contMDiff_fst).add contMDiff_snd
  have hG := contMDiff_retractionGraph he hr
  have hcomp : p ∘ (fun x : U => retractionGraph e r x) = Subtype.val := by
    funext x
    change e (r x) + ((x : F) - e (r x)) = x
    abel
  have hd := mfderiv_comp x (hp.mdifferentiable (by simp) _) (hG.mdifferentiable (by simp) x)
  rw [hcomp, mfderiv_subtype_val] at hd
  intro v w hvw
  have hv := DFunLike.congr_fun hd v
  have hw := DFunLike.congr_fun hd w
  exact hv.trans ((congrArg (mfderiv (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, F) p
    (retractionGraph e r x)) hvw).trans hw.symm)

end DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Riemannian

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

def retractionMetric (g : SmoothRiemannianMetric I M)
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {r : F → M} {U : TopologicalSpace.Opens F}
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r U) : SmoothRiemannianMetric 𝓘(ℝ, F) U :=
  (g.prod (euclideanMetric (E := F))).pullback
    (fun x : U => retractionGraph e r x) (contMDiff_retractionGraph he hr)
    (injective_mfderiv_retractionGraph he hr)

end DifferentialGeometry.Geometry.Riemannian

noncomputable section
open Manifold Set
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Riemannian
variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem retractionMetric_inner_map
    (g : SmoothRiemannianMetric I M)
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {r : F → M} {U : TopologicalSpace.Opens F}
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r U)
    (hEU : range e ⊆ U) (hleft : ∀ p, r (e p) = p)
    (p : M) (v w : TangentSpace I p) :
    (retractionMetric g he hr).inner ⟨e p, hEU (mem_range_self p)⟩
      (mfderiv I 𝓘(ℝ, F) e p v) (mfderiv I 𝓘(ℝ, F) e p w) = g.inner p v w := by
  let j : M → U := fun q => ⟨e q, hEU (mem_range_self q)⟩
  let G : U → M × F := fun x => retractionGraph e r x
  have hG : ContMDiff 𝓘(ℝ, F) (I.prod 𝓘(ℝ, F)) ∞ G :=
    contMDiff_retractionGraph he hr
  have hcomp : G ∘ j = (fun q : M => (q, (0 : F))) := by
    funext q
    apply Prod.ext
    · change r (e q) = q
      exact hleft q
    · change e q - e (r (e q)) = 0
      rw [hleft q]
      exact sub_self _
  have hder := mfderiv_comp p
      (hG.mdifferentiableAt (by simp))
      ((MDifferentiableAt.subtypeVal_comp_iff (I := I) (J := 𝓘(ℝ, F)) j p).mp
        (he.mdifferentiableAt (by simp)))
  have hder' : mfderiv I (I.prod 𝓘(ℝ, F)) (G ∘ j) p =
      (mfderiv 𝓘(ℝ, F) (I.prod 𝓘(ℝ, F)) G (j p)).comp
        (mfderiv I 𝓘(ℝ, F) (fun q => e q) p) := by
    rw [← mfderiv_subtypeVal_comp j p] at hder
    exact hder
  have hpoint (z : TangentSpace I p) :
      mfderiv 𝓘(ℝ, F) (I.prod 𝓘(ℝ, F)) G (j p)
        (mfderiv I 𝓘(ℝ, F) (fun q => e q) p z) = (z, 0) := by
    have hz := DFunLike.congr_fun hder' z
    rw [hcomp] at hz
    rw [mfderiv_prod_left] at hz
    exact hz.symm
  change (g.prod (euclideanMetric (E := F))).inner (G (j p))
    (mfderiv 𝓘(ℝ, F) (I.prod 𝓘(ℝ, F)) G (j p)
      (mfderiv I 𝓘(ℝ, F) e p v))
    (mfderiv 𝓘(ℝ, F) (I.prod 𝓘(ℝ, F)) G (j p)
      (mfderiv I 𝓘(ℝ, F) e p w)) = _
  rw [hpoint v, hpoint w]
  have hpG : G (j p) = (p, 0) := congrFun hcomp p
  change (g.prod (euclideanMetric (E := F))).inner (G (j p))
    (show E × F from (v, 0)) (show E × F from (w, 0)) = _
  rw [hpG]
  have hprod := SmoothRiemannianMetric.prod_inner g (euclideanMetric (E := F)) (p, 0)
    (show TangentSpace (I.prod 𝓘(ℝ, F)) (p, (0 : F)) from (v, 0))
    (show TangentSpace (I.prod 𝓘(ℝ, F)) (p, (0 : F)) from (w, 0))
  apply hprod.trans
  change g.inner p v w + (euclideanMetric (E := F)).inner 0 0 0 = g.inner p v w
  rw [map_zero, add_zero]


theorem retractionMetric_inner_comp
    {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
    [TopologicalSpace N] [ChartedSpace H' N]
    (g : SmoothRiemannianMetric I M)
    {e : M → F} (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    {r : F → M} {U : TopologicalSpace.Opens F}
    (hr : ContMDiffOn 𝓘(ℝ, F) I ∞ r U)
    (hEU : range e ⊆ U) (hleft : ∀ p, r (e p) = p)
    {c : N → M} (hc : ContMDiff J I ∞ c) (x : N) (v w : TangentSpace J x) :
    (retractionMetric g he hr).inner ⟨e (c x), hEU (mem_range_self (c x))⟩
      (mfderiv J 𝓘(ℝ, F) (e ∘ c) x v) (mfderiv J 𝓘(ℝ, F) (e ∘ c) x w) =
        g.inner (c x) (mfderiv J I c x v) (mfderiv J I c x w) := by
  rw [mfderiv_comp_apply x (he.mdifferentiableAt (by simp))
      (hc.mdifferentiableAt (by simp)) v,
    mfderiv_comp_apply x (he.mdifferentiableAt (by simp))
      (hc.mdifferentiableAt (by simp)) w]
  exact retractionMetric_inner_map g he hr hEU hleft (c x) _ _

end DifferentialGeometry.Geometry.Riemannian
