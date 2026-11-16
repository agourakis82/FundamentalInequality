/-
Copyright (c) 2026 Demetrios Chiuratto Agourakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Demetrios Chiuratto Agourakis
-/
module

public import Examples.PadicSqrtP.Basic
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# Ramification in `ℚ_p(√p)`

This file equips `ℚ_[p](√p)` with the spectral valuative relation extending
the standard `p`-adic relation. The value of `√p` does not lie in the image of
the base value group: otherwise its square would give an element of `ℚ_[p]`
with twice an integral `p`-adic valuation equal to one. The fundamental
inequality then gives `e = 2`, `f = 1`, and no defect.

The compatible valuative relation is unique by completeness of `ℚ_[p]` and
`ArtinSchreierBridge.unique_valuativeRel_of_complete`.

## References

* [J.-P. Serre, *Local Fields*][serreLocalFields], Chapter II, §2.
* [N. Bourbaki, *Commutative Algebra*][bourbaki1989b], Chapter VI.
-/

@[expose] public section

noncomputable section

open Polynomial ValuativeRel ValuativeExtension
open scoped ValuativeRel NNReal

namespace PadicSqrtP

open ArtinSchreierBridge

variable (p : ℕ) [Fact p.Prime]

abbrev Base := ℚ_[p]
abbrev RootExtension := Extension p

instance extensionAlgebraic : Algebra.IsAlgebraic (Base p) (RootExtension p) :=
  Algebra.IsAlgebraic.of_finite (Base p) (RootExtension p)

/-- The spectral valuation on `ℚ_[p](√p)`. -/
def spectralValuation : Valuation (RootExtension p) ℝ≥0 where
  toFun x := ⟨spectralNorm (Base p) (RootExtension p) x, spectralNorm_nonneg x⟩
  map_zero' := by ext; exact spectralNorm_zero
  map_one' := by ext; exact spectralNorm_one
  map_mul' x y := by ext; exact spectralAlgNorm_mul x y
  map_add_le_max' x y := isNonarchimedean_spectralNorm x y

instance extensionValuativeRel : ValuativeRel (RootExtension p) :=
  .ofValuation (spectralValuation p)

/-- The spectral relation extends Mathlib's standard `p`-adic valuative relation. -/
instance baseExtensionValuativeExtension :
    ValuativeExtension (Base p) (RootExtension p) where
  vle_iff_vle x y := by
    change spectralNorm (Base p) (RootExtension p) (algebraMap _ _ x) ≤
      spectralNorm (Base p) (RootExtension p) (algebraMap _ _ y) ↔
        Padic.mulValuation x ≤ Padic.mulValuation y
    rw [spectralNorm_extends, spectralNorm_extends]
    simpa only [not_lt] using
      not_congr (Padic.norm_lt_norm_iff_mulValuation_lt (x := y) (y := x))

theorem base_vle_iff_norm (x y : Base p) : x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := by
  change Padic.mulValuation x ≤ Padic.mulValuation y ↔ ‖x‖ ≤ ‖y‖
  simpa only [not_lt] using
    (not_congr (Padic.norm_lt_norm_iff_mulValuation_lt (x := y) (y := x))).symm

/-- The spectral relation is the unique valuative relation on `ℚ_[p](√p)`
compatible with the standard `p`-adic relation. -/
theorem unique_extension (other : ValuativeRel (RootExtension p))
    (h : letI := other; ValuativeExtension (Base p) (RootExtension p)) :
    other = extensionValuativeRel p := by
  let := other
  let := h
  have : IsRankLeOne (RootExtension p) :=
    ValuativeRel.IsRankLeOne.of_finiteDimensional (Base p) (RootExtension p)
  have : IsNontrivial (RootExtension p) :=
    ValuativeRel.IsNontrivial.of_valuativeExtension (Base p) (RootExtension p)
  have hcmp := unique_valuativeRel_of_complete (K := Base p) (L := RootExtension p)
    (base_vle_iff_norm p) other h
  refine ValuativeRel.ext ?_
  funext x y
  exact propext ((hcmp x y).trans Iff.rfl)

/-- Every compatible valuative relation equals the spectral relation. -/
theorem extension_eq_spectral
    (w : Extensions (Base p) (RootExtension p)) :
    w.val = extensionValuativeRel p :=
  unique_extension p w.val w.property

/-- The canonical generator of `ℚ_[p](√p)`. -/
def sqrtP : RootExtension p := AdjoinRoot.root (polynomial p)

theorem sqrtP_sq :
    sqrtP p ^ 2 = algebraMap (Base p) (RootExtension p) (p : Base p) :=
  root_sq p

theorem sqrtP_ne_zero : sqrtP p ≠ 0 := by
  intro h
  have hs := sqrtP_sq p
  rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    ((algebraMap (Base p) (RootExtension p)).injective (by simpa using hs.symm))

/-- The value of `√p` is not in the image of the value group of `ℚ_[p]`. -/
theorem sqrtP_value_not_mem_range :
    valuation (RootExtension p) (sqrtP p) ∉
      Set.range (mapValueGroupWithZero (Base p) (RootExtension p)) := by
  rintro ⟨γ, hγ⟩
  obtain ⟨x, hx⟩ := valuation_surjective (K := Base p) γ
  have hval : valuation (RootExtension p)
      (algebraMap (Base p) (RootExtension p) x) =
        valuation (RootExtension p) (sqrtP p) := by
    calc
      valuation (RootExtension p) (algebraMap (Base p) (RootExtension p) x) =
          mapValueGroupWithZero (Base p) (RootExtension p) (valuation (Base p) x) := by
            rw [mapValueGroupWithZero_valuation]
      _ = mapValueGroupWithZero (Base p) (RootExtension p) γ := by rw [hx]
      _ = valuation (RootExtension p) (sqrtP p) := hγ
  have hx0 : x ≠ 0 := by
    intro hxz
    rw [hxz, map_zero, map_zero] at hval
    exact sqrtP_ne_zero p ((valuation (RootExtension p)).zero_iff.mp hval.symm)
  have hsquare : valuation (RootExtension p)
      (algebraMap (Base p) (RootExtension p) (x ^ 2)) =
        valuation (RootExtension p)
          (algebraMap (Base p) (RootExtension p) (p : Base p)) := by
    calc
      valuation (RootExtension p) (algebraMap (Base p) (RootExtension p) (x ^ 2)) =
          valuation (RootExtension p)
            (algebraMap (Base p) (RootExtension p) x) ^ 2 := by simp
      _ = valuation (RootExtension p) (sqrtP p) ^ 2 := by rw [hval]
      _ = valuation (RootExtension p) (sqrtP p ^ 2) := by rw [map_pow]
      _ = valuation (RootExtension p)
          (algebraMap (Base p) (RootExtension p) (p : Base p)) := by rw [sqrtP_sq]
  have hbase : valuation (Base p) (x ^ 2) = valuation (Base p) (p : Base p) := by
    apply (mapValueGroupWithZero_strictMono
      (A := Base p) (B := RootExtension p)).injective
    simpa only [mapValueGroupWithZero_valuation] using hsquare
  have hveq : x ^ 2 =ᵥ (p : Base p) :=
    (Valuation.veq_iff_eq (v := valuation (Base p))).mpr hbase
  have hmul : Padic.mulValuation (x ^ 2) = Padic.mulValuation (p : Base p) :=
    (Valuation.veq_iff_eq (v := Padic.mulValuation)).mp hveq
  have hlog := congrArg WithZero.log hmul
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  simp [Padic.mulValuation, hx0, hp0, Padic.valuation_pow] at hlog
  omega

theorem mapValueGroupWithZero_not_surjective :
    ¬ Function.Surjective (mapValueGroupWithZero (Base p) (RootExtension p)) := by
  intro h
  exact sqrtP_value_not_mem_range p (h (valuation (RootExtension p) (sqrtP p)))

/-- The ramification index of `ℚ_[p](√p)/ℚ_[p]` is two. -/
theorem ramificationIdx_eq_two :
    ramificationIdx (Base p) (RootExtension p) = 2 := by
  have hne_one : ramificationIdx (Base p) (RootExtension p) ≠ 1 := by
    intro h
    exact mapValueGroupWithZero_not_surjective p (ramificationIdx_eq_one_iff.mp h)
  have hpos := one_le_ramificationIdx (K := Base p) (L := RootExtension p)
  have hfpos := inertiaDeg_pos (K := Base p) (L := RootExtension p)
  have hbound := ramificationIdx_mul_inertiaDeg_le_finrank
    (K := Base p) (L := RootExtension p)
  rw [finrank_eq_two] at hbound
  have hele : ramificationIdx (Base p) (RootExtension p) ≤ 2 :=
    (Nat.le_mul_of_pos_right _ hfpos).trans hbound
  omega

/-- The inertia degree of `ℚ_[p](√p)/ℚ_[p]` is one. -/
theorem inertiaDeg_eq_one : inertiaDeg (Base p) (RootExtension p) = 1 := by
  have hpos := inertiaDeg_pos (K := Base p) (L := RootExtension p)
  have hbound := ramificationIdx_mul_inertiaDeg_le_finrank
    (K := Base p) (L := RootExtension p)
  rw [ramificationIdx_eq_two, finrank_eq_two] at hbound
  omega

/-- The fundamental inequality is an equality for `ℚ_[p](√p)/ℚ_[p]`. -/
theorem ramificationIdx_mul_inertiaDeg_eq_finrank :
    ramificationIdx (Base p) (RootExtension p) *
      inertiaDeg (Base p) (RootExtension p) =
        Module.finrank (Base p) (RootExtension p) := by
  rw [ramificationIdx_eq_two, inertiaDeg_eq_one, finrank_eq_two]

end PadicSqrtP
