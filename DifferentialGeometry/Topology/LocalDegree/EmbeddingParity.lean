/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.LocalDegree.EmbeddingComposition
import DifferentialGeometry.Topology.LocalDegree.InjectiveCarrierSign

open Set Filter
open scoped Topology

noncomputable section

namespace DifferentialGeometry.LocalDegree

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (d + 1))

def embeddingOrientationParity {U : Set E} (hU : IsOpen U)
    {f : E → E} (hf : ContinuousOn f U) (hinj : InjOn f U) (x : U) : ZMod 2 :=
  if euclideanLocalDegree (fun z => f z - f x) x
    (isolatedZero_sub_of_injOn hU hf hinj x.2) = 1 then 0 else 1

theorem embeddingOrientationParity_eq_zero_iff {U : Set E} (hU : IsOpen U)
    {f : E → E} (hf : ContinuousOn f U) (hinj : InjOn f U) (x : U) :
    embeddingOrientationParity hU hf hinj x = 0 ↔
      euclideanLocalDegree (fun z => f z - f x) x
        (isolatedZero_sub_of_injOn hU hf hinj x.2) = 1 := by
  simp [embeddingOrientationParity]

theorem embeddingOrientationParity_eq_one_iff {U : Set E} (hU : IsOpen U)
    {f : E → E} (hf : ContinuousOn f U) (hinj : InjOn f U) (x : U) :
    embeddingOrientationParity hU hf hinj x = 1 ↔
      euclideanLocalDegree (fun z => f z - f x) x
        (isolatedZero_sub_of_injOn hU hf hinj x.2) = -1 := by
  rcases euclideanLocalDegree_eq_one_or_neg_one_of_injOn hU hf hinj x.2 with hp | hn
  · simp [embeddingOrientationParity, hp]
  · simp [embeddingOrientationParity, hn]

theorem isLocallyConstant_embeddingOrientationParity {U : Set E} (hU : IsOpen U)
    {f : E → E} (hf : ContinuousOn f U) (hinj : InjOn f U) :
    IsLocallyConstant (embeddingOrientationParity hU hf hinj) :=
  (isLocallyConstant_euclideanLocalDegree_sub_of_injOn hU hf hinj).comp
    (fun k : ℤ => if k = 1 then (0 : ZMod 2) else 1)

theorem embeddingOrientationParity_eq_of_isPreconnected
    {U A : Set E} (hU : IsOpen U) {f : E → E}
    (hf : ContinuousOn f U) (hinj : InjOn f U)
    (hA : IsPreconnected A) (hAU : A ⊆ U)
    {x y : E} (hx : x ∈ A) (hy : y ∈ A) :
    embeddingOrientationParity hU hf hinj ⟨x, hAU hx⟩ =
      embeddingOrientationParity hU hf hinj ⟨y, hAU hy⟩ := by
  unfold embeddingOrientationParity
  rw [euclideanLocalDegree_sub_eq_of_isPreconnected hU hf hinj hA hAU hx hy]

theorem embeddingOrientationParity_comp
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {f g : E → E} (hf : ContinuousOn f U) (hfi : InjOn f U)
    (hg : ContinuousOn g V) (hgi : InjOn g V) (hm : MapsTo f U V) (x : U) :
    embeddingOrientationParity hU (hg.comp hf hm) (hgi.comp hfi hm) x =
      embeddingOrientationParity hU hf hfi x +
        embeddingOrientationParity hV hg hgi ⟨f x, hm x.2⟩ := by
  unfold embeddingOrientationParity
  erw [euclideanLocalDegree_sub_comp_of_injOn hU hV hf hfi hg hgi hm x.2]
  rcases euclideanLocalDegree_eq_one_or_neg_one_of_injOn hU hf hfi x.2 with hp | hn
  · rcases euclideanLocalDegree_eq_one_or_neg_one_of_injOn hV hg hgi (hm x.2) with hgp | hgn
    · simp [hp, hgp]
    · simp [hp, hgn]
  · rcases euclideanLocalDegree_eq_one_or_neg_one_of_injOn hV hg hgi (hm x.2) with hgp | hgn
    · simp [hn, hgp]
    · simp [hn, hgn, show (1 : ZMod 2) + 1 = 0 from by decide]

theorem embeddingOrientationParity_congr
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {f g : E → E} (hf : ContinuousOn f U) (hfi : InjOn f U)
    (hg : ContinuousOn g V) (hgi : InjOn g V) {x : E}
    (hxU : x ∈ U) (hxV : x ∈ V) (hfg : f =ᶠ[𝓝 x] g) :
    embeddingOrientationParity hU hf hfi ⟨x, hxU⟩ =
      embeddingOrientationParity hV hg hgi ⟨x, hxV⟩ := by
  have hfgx : f x = g x := hfg.self_of_nhds
  have heq : (fun z => f z - f x) =ᶠ[𝓝 x] (fun z => g z - g x) := by
    filter_upwards [hfg] with z hz
    rw [hz, hfgx]
  unfold embeddingOrientationParity
  rw [euclideanLocalDegree_congr _ _ heq]

theorem embeddingOrientationParity_id {U : Set E} (hU : IsOpen U) (x : U) :
    embeddingOrientationParity hU continuousOn_id (injOn_id U) x = 0 := by
  have h := embeddingOrientationParity_comp hU hU continuousOn_id (injOn_id U)
    continuousOn_id (injOn_id U) (mapsTo_id U) x
  change embeddingOrientationParity hU continuousOn_id (injOn_id U) x =
    embeddingOrientationParity hU continuousOn_id (injOn_id U) x +
      embeddingOrientationParity hU continuousOn_id (injOn_id U) x at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)
end DifferentialGeometry.LocalDegree
