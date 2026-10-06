import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.HalfCollarOfEmbeddingHCOL
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Presentation

/-!
# `BoundaryTori` from the embedded labelled products (lane S-COLLAR, G2, suffix `_HCOL`)

The three port-collar compatibilities of the BD0 skeleton (`cuspCoresData_of_same_product_BGR`,
`cuspCoresDataLevel_BGR`: `external_end`, `collar_owned`, `collar_closure_off`) in the form of the
embeddings `Φ i = (piece i).map ∘ product i : T² × [0, 1] → W`.

* **`boundaryTori_of_embeddings_HCOL`**: `n` smooth embeddings `Φ i : T² × [0, 1] → W` with pairwise
  disjoint ranges and `Φ i (t, 0) ∈ ∂W` ⟹ a `BoundaryTori W n` `Et` with
  `Et.torusMap i t = Φ i (t, 0)` (`external_end`), `(Et.collar i).target ⊆ range (Φ i)`
  (`collar_owned`), and `closure (Et.collar i).target` disjoint from `Φ i (T² × {1})`
  (`collar_closure_off`);
* the collars are the half-collars `halfCollar_of_boundary_embedding_HCOL` (target
  `Φ i '' {p₂ < 1/2}`, `collar i (t, s) = Φ i (t, s/2)`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff
open Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.GraphManifold.Assembly

namespace DifferentialGeometry.Topology.HalfCollarHCOL

universe u

/-- **Closure of the half-collar misses the far end.**  For an injective continuous `Φ` on
`T² × [0, 1]`, the closure of `Φ '' {p₂ < 1/2}` is disjoint from `Φ '' {p₂ = 1}` (it lies in the
compact `Φ '' {p₂ ≤ 1/2}`). -/
theorem closure_halfCollar_disjoint_HCOL {X : Type*} [TopologicalSpace X] [T2Space X]
    (Φ : Torus × Icc (0 : ℝ) 1 → X) (hc : Continuous Φ) (hinj : Injective Φ) :
    Disjoint (closure (Φ '' {p | (p.2 : ℝ) < 1 / 2}))
      (range fun t : Torus => Φ (t, iccEnd true)) := by
  have hK : IsCompact (Φ '' {p : Torus × Icc (0 : ℝ) 1 | (p.2 : ℝ) ≤ 1 / 2}) :=
    ((isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const).isCompact).image
      hc
  have hcl : closure (Φ '' {p | (p.2 : ℝ) < 1 / 2}) ⊆
      Φ '' {p : Torus × Icc (0 : ℝ) 1 | (p.2 : ℝ) ≤ 1 / 2} :=
    closure_minimal (image_mono fun p (hp : ((p.2 : Icc (0 : ℝ) 1) : ℝ) < 1 / 2) =>
      show ((p.2 : Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2 from hp.le) hK.isClosed
  refine Disjoint.mono_left hcl ?_
  rw [Set.disjoint_left]
  rintro _ ⟨p, hp, rfl⟩ ⟨t, ht⟩
  have hpt : p = (t, iccEnd true) := hinj ht.symm
  have h1 : ((p.2 : Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2 := hp
  rw [hpt] at h1
  have h2 : ((iccEnd true : Icc (0 : ℝ) 1) : ℝ) = 1 := by simp [iccEnd]
  change ((iccEnd true : Icc (0 : ℝ) 1) : ℝ) ≤ 1 / 2 at h1
  linarith

/-- **`BoundaryTori` from the embedded labelled products.** -/
theorem boundaryTori_of_embeddings_HCOL (W : CompactCarrier.{u}) {n : ℕ}
    (Φ : Fin n → Torus × Icc (0 : ℝ) 1 → W.Carrier)
    (hΦ : ∀ i, IsSmoothEmbedding (torusModel.prod (𝓡∂ 1)) W.model ∞ (Φ i))
    (h0 : ∀ i t, W.model.IsBoundaryPoint (Φ i (t, iccEnd false)))
    (hdisj : Pairwise fun i j => Disjoint (range (Φ i)) (range (Φ j))) :
    ∃ Et : BoundaryTori W n,
      (∀ i t, Φ i (t, iccEnd false) = Et.torusMap i t) ∧
      (∀ i, (Et.collar i).target ⊆ range (Φ i)) ∧
      (∀ i, Disjoint (closure (Et.collar i).target)
        (range fun t : Torus => Φ i (t, iccEnd true))) := by
  choose d hs ht hv using fun i => halfCollar_of_boundary_embedding_HCOL W (Φ i) (hΦ i) (h0 i)
  have hz : ∀ i t, d i (t, halfZero) = Φ i (t, iccEnd false) := fun i t =>
    hv i t halfZero (iccEnd false) (by change (0 : ℝ) < 1; norm_num)
      (by change ((iccEnd false : Icc (0 : ℝ) 1) : ℝ) = 0 / 2; simp [iccEnd])
  have hsub : ∀ i, (d i).target ⊆ range (Φ i) := fun i => by
    rw [ht i]
    exact image_subset_range _ _
  refine ⟨{ collar := d
            source_eq := hs
            boundary_zero := fun i t => by rw [hz]; exact h0 i t
            disjoint := fun i j hij => (hdisj hij).mono (hsub i) (hsub j) }, ?_, hsub, ?_⟩
  · intro i t
    exact (hz i t).symm
  · intro i
    change Disjoint (closure (d i).target) _
    rw [ht i]
    exact closure_halfCollar_disjoint_HCOL (Φ i) (hΦ i).contMDiff.continuous
      (hΦ i).isEmbedding.injective

end DifferentialGeometry.Topology.HalfCollarHCOL
