import DifferentialGeometry.Geometry.Metric.ExteriorPower
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

noncomputable section

open scoped BigOperators RealInnerProductSpace ContDiff

namespace exteriorPower

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem contDiff_ιMulti (k : ℕ) (n : ℕ∞ω) :
    ContDiff ℝ n (ιMulti ℝ k (M := E)) := by
  let b := stdOrthonormalBasis ℝ (⋀[ℝ]^k E)
  have h (v : Fin k → E) :
      (∑ i, musicalEquiv k (b i) v • b i) = ιMulti ℝ k v := by
    simpa only [musicalEquiv_apply] using b.sum_repr' (ιMulti ℝ k v)
  have hs : ContDiff ℝ n (fun v : Fin k → E => ∑ i, musicalEquiv k (b i) v • b i) :=
    ContDiff.sum fun i _ =>
      (musicalEquiv k (b i)).toContinuousMultilinearMap.contDiff.smul contDiff_const
  convert hs using 1
  exact (funext h).symm

def mapContinuousLinearMap (k : ℕ) (f : E →L[ℝ] F) : (⋀[ℝ]^k E) →L[ℝ] ⋀[ℝ]^k F :=
  (map k f.toLinearMap).toContinuousLinearMap

@[simp]
theorem mapContinuousLinearMap_apply (k : ℕ) (f : E →L[ℝ] F) (u : ⋀[ℝ]^k E) :
    mapContinuousLinearMap k f u = map k f.toLinearMap u := rfl

theorem mapContinuousLinearMap_ιMulti (k : ℕ) (f : E →L[ℝ] F) (v : Fin k → E) :
    mapContinuousLinearMap k f (ιMulti ℝ k v) = ιMulti ℝ k (fun i => f (v i)) :=
  map_apply_ιMulti f.toLinearMap v

@[simp]
theorem mapContinuousLinearMap_id (k : ℕ) :
    mapContinuousLinearMap k (ContinuousLinearMap.id ℝ E) =
      ContinuousLinearMap.id ℝ (⋀[ℝ]^k E) := by
  apply ContinuousLinearMap.ext
  intro u
  change map k (LinearMap.id : E →ₗ[ℝ] E) u = u
  rw [map_id]
  rfl

theorem mapContinuousLinearMap_comp {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    (k : ℕ) (f : E →L[ℝ] F) (g : F →L[ℝ] G) :
    mapContinuousLinearMap k (g.comp f) =
      (mapContinuousLinearMap k g).comp (mapContinuousLinearMap k f) := by
  apply ContinuousLinearMap.ext
  intro u
  change map k (g.toLinearMap.comp f.toLinearMap) u =
    map k g.toLinearMap (map k f.toLinearMap u)
  rw [map_comp]
  rfl

theorem mapContinuousLinearMap_smul (k : ℕ) (c : ℝ) (f : E →L[ℝ] F) :
    mapContinuousLinearMap k (c • f) = c ^ k • mapContinuousLinearMap k f := by
  apply ContinuousLinearMap.coe_injective
  change map k (c • f).toLinearMap = c ^ k • map k f.toLinearMap
  apply linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.smul_apply, map_apply_ιMulti]
  change ιMulti ℝ k (fun i => c • f (v i)) = c ^ k • ιMulti ℝ k (fun i => f (v i))
  rw [(ιMulti ℝ k).map_smul_univ]
  simp

theorem contDiff_mapContinuousLinearMap (k : ℕ) (n : ℕ∞ω) :
    ContDiff ℝ n (mapContinuousLinearMap (E := E) (F := F) k) := by
  rw [contDiff_clm_apply_iff]
  intro u
  have hu : u ∈ Submodule.span ℝ (Set.range (ιMulti ℝ k (M := E))) := by
    rw [ιMulti_span]
    trivial
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨v, rfl⟩ := hu
    simp_rw [mapContinuousLinearMap_ιMulti]
    exact (contDiff_ιMulti k n).comp
      (contDiff_pi.mpr fun i => contDiff_id.clm_apply contDiff_const)
  | zero =>
    simp only [map_zero]
    exact contDiff_const
  | add u v _ _ hu hv =>
    simp only [map_add]
    exact hu.add hv
  | smul c u _ hu =>
    simp only [map_smul]
    exact (contDiff_const (c := c)).smul hu

theorem contDiff_mapContinuousLinearMap_apply (k : ℕ) (n : ℕ∞ω) :
    ContDiff ℝ n (fun p : (E →L[ℝ] F) × (⋀[ℝ]^k E) =>
      mapContinuousLinearMap k p.1 p.2) :=
  ((contDiff_mapContinuousLinearMap k n).comp contDiff_fst).clm_apply contDiff_snd

end exteriorPower
