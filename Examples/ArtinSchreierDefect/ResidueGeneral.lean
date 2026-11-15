/-
Copyright (c) 2026 Demetrios Chiuratto Agourakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Demetrios Chiuratto Agourakis
-/
module

public import Examples.ArtinSchreierDefect.Valuation
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Subring
public import Mathlib.Algebra.CharP.Quotient
public import Mathlib.FieldTheory.Perfect

/-!
# Residue degree one for prime-degree Artin--Schreier defect extensions

For every prime p, this file constructs a p-th root of t⁻¹ in the perfect hull,
rescales the Artin--Schreier generator to a unit, and proves that the resulting
residue-field extension has degree one.
-/

@[expose] public section

noncomputable section
open Polynomial ValuativeRel ValuativeExtension
open scoped LaurentSeries WithZero ValuativeRel BigOperators NNReal

namespace ArtinSchreierDefect.General

open ArtinSchreierBridge

variable (p : ℕ) [Fact p.Prime]


def IsLevelOne (x : Hull p) : Prop := ∃ y : Base p, x ^ p = algebraMap (Base p) (Hull p) y

theorem isLevelOne_zero : IsLevelOne p 0 := ⟨0, by simp [(Fact.out : p.Prime).ne_zero]⟩

theorem isLevelOne_one : IsLevelOne p 1 := ⟨1, by simp⟩

theorem isLevelOne_algebraMap (y : Base p) :
    IsLevelOne p (algebraMap (Base p) (Hull p) y) :=
  ⟨y ^ p, by rw [← map_pow]⟩

theorem isLevelOne_add {x y : Hull p} (hx : IsLevelOne p x) (hy : IsLevelOne p y) :
    IsLevelOne p (x + y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a + b, ?_⟩
  rw [add_pow_char (p := p), ha, hb, map_add]

theorem isLevelOne_mul {x y : Hull p} (hx : IsLevelOne p x) (hy : IsLevelOne p y) :
    IsLevelOne p (x * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a * b, ?_⟩
  rw [mul_pow, ha, hb, map_mul]

theorem isLevelOne_inv {x : Hull p} (hx : IsLevelOne p x) : IsLevelOne p x⁻¹ := by
  obtain ⟨a, ha⟩ := hx
  by_cases hx0 : x = 0
  · simpa [hx0] using isLevelOne_zero p
  refine ⟨a⁻¹, ?_⟩
  rw [inv_pow, ha, map_inv₀]

theorem isLevelOne_pow {x : Hull p} (hx : IsLevelOne p x) (n : ℕ) :
    IsLevelOne p (x ^ n) := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨a ^ n, ?_⟩
  rw [← pow_mul, Nat.mul_comm n p, pow_mul, ha, ← map_pow]

theorem exists_pow_in_base (x : Hull p) :
    ∃ n : ℕ, ∃ y : Base p, x ^ (p ^ n) = algebraMap (Base p) (Hull p) y := by
  have hx : (x : AlgebraicClosure (Base p)) ∈
      perfectClosure (Base p) (AlgebraicClosure (Base p)) := x.2
  rw [mem_perfectClosure_iff_pow_mem (q := p)] at hx
  obtain ⟨n, ⟨y, hy⟩⟩ := hx
  refine ⟨n, y, ?_⟩
  exact Subtype.ext (by simpa [map_pow] using hy.symm)

theorem one_vlt_inverseT_base : (1 : Base p) <ᵥ inverseT p := by
  have hval : (Valued.v : Valuation (Base p) ℤᵐ⁰) (inverseT p) = WithZero.exp (1 : ℤ) :=
    ArtinSchreierDefect.inverseT_value p
  have hlt : (1 : ℤᵐ⁰) < (Valued.v : Valuation (Base p) ℤᵐ⁰) (inverseT p) := by
    rw [hval]
    change WithZero.exp (0 : ℤ) < WithZero.exp (1 : ℤ)
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  exact (Valuation.vlt_iff_lt (v := (Valued.v : Valuation (Base p) ℤᵐ⁰))).mpr
    (by simpa using hlt)

theorem not_pth_veq_inverseT (x : Base p) : ¬ x ^ p =ᵥ inverseT p := by
  intro h
  have hv := (Valuation.veq_iff_eq
    (v := (Valued.v : Valuation (Base p) ℤᵐ⁰))).mp h
  have hval : (Valued.v x) ^ p = WithZero.exp (1 : ℤ) := by
    rw [← map_pow, hv, ArtinSchreierDefect.inverseT_value p]
  exact ArtinSchreierDefect.exp_one_not_pth_power p (Valued.v x) hval

theorem not_pth_veq_inverseT_pow_pred (x : Base p) :
    ¬ x ^ p =ᵥ (inverseT p) ^ (p - 1) := by
  intro h
  have hv := (Valuation.veq_iff_eq
    (v := (Valued.v : Valuation (Base p) ℤᵐ⁰))).mp h
  have hval : (Valued.v x) ^ p = WithZero.exp ((p - 1 : ℕ) : ℤ) := by
    rw [← map_pow, hv, map_pow, ArtinSchreierDefect.inverseT_value p,
      ← WithZero.exp_nsmul]
    simp
  have hh := congrArg WithZero.log hval
  have hh' : (p : ℤ) * WithZero.log (Valued.v x) = ((p - 1 : ℕ) : ℤ) := by
    simpa [WithZero.log_pow] using hh
  rw [Int.ofNat_sub (Fact.out : p.Prime).one_le] at hh'
  have hdvd : (p : ℤ) ∣ (p : ℤ) - 1 :=
    ⟨WithZero.log (Valued.v x), hh'.symm⟩
  have hone : (p : ℤ) ∣ 1 := by
    convert dvd_sub (dvd_refl (p : ℤ)) hdvd using 1
    ring
  have hone' : p ∣ 1 := by exact_mod_cast hone
  exact (Nat.not_dvd_of_pos_of_lt Nat.one_pos (Fact.out : p.Prime).one_lt) hone'

theorem exists_invTRoot : ∃ σ : Hull p,
    σ ^ p = algebraMap (Base p) (Hull p) (inverseT p) :=
  surjective_frobenius (Hull p) p (algebraMap (Base p) (Hull p) (inverseT p))

noncomputable def invTRoot : Hull p := (exists_invTRoot p).choose

theorem invTRoot_pow : (invTRoot p) ^ p =
    algebraMap (Base p) (Hull p) (inverseT p) :=
  (exists_invTRoot p).choose_spec

theorem isLevelOne_invTRoot : IsLevelOne p (invTRoot p) :=
  ⟨inverseT p, invTRoot_pow p⟩

theorem invTRoot_ne_zero : invTRoot p ≠ 0 := by
  intro h
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpow := invTRoot_pow p
  rw [h, zero_pow hp0] at hpow
  have h0 : algebraMap (Base p) (Hull p) (inverseT p) = 0 := hpow.symm
  have hinv : inverseT p ≠ 0 :=
    HahnSeries.single_ne_zero (one_ne_zero (α := ZMod p))
  exact hinv ((algebraMap (Base p) (Hull p)).injective (by simpa using h0))

theorem one_vlt_inverseT_hull :
    (1 : Hull p) <ᵥ algebraMap (Base p) (Hull p) (inverseT p) := by
  have h : ¬ algebraMap (Base p) (Hull p) (inverseT p) ≤ᵥ
      algebraMap (Base p) (Hull p) (1 : Base p) := by
    rw [ValuativeExtension.vle_iff_vle (A := Base p) (B := Hull p)]
    exact ValuativeRel.not_vle.mpr (one_vlt_inverseT_base p)
  simpa using (ValuativeRel.not_vle.mp h)

theorem one_vlt_invTRoot : (1 : Hull p) <ᵥ invTRoot p := by
  have hpow : (1 : Hull p) <ᵥ (invTRoot p) ^ p := by
    rw [invTRoot_pow]
    exact one_vlt_inverseT_hull p
  by_contra hle
  have hle' : invTRoot p ≤ᵥ (1 : Hull p) := ValuativeRel.not_vlt.mp hle
  have : (invTRoot p) ^ p ≤ᵥ (1 : Hull p) ^ p := pow_vle_pow hle' p
  simp only [one_pow] at this
  exact (ValuativeRel.not_vle.mpr hpow) this

noncomputable def asRoot : Extension p :=
  AdjoinRoot.root (ArtinSchreierDefect.standardPolynomial p)

noncomputable def invTRootE : Extension p :=
  algebraMap (Hull p) (Extension p) (invTRoot p)

theorem invTRootE_ne_zero : invTRootE p ≠ 0 := by
  intro h
  exact invTRoot_ne_zero p
    ((algebraMap (Hull p) (Extension p)).injective (by simpa [invTRootE] using h))

theorem invTRootE_pow : (invTRootE p) ^ p =
    algebraMap (Hull p) (Extension p)
      (algebraMap (Base p) (Hull p) (inverseT p)) := by
  rw [invTRootE, ← map_pow, invTRoot_pow]

theorem one_vlt_invTRootE : (1 : Extension p) <ᵥ invTRootE p := by
  have h : ¬ invTRootE p ≤ᵥ algebraMap (Hull p) (Extension p) (1 : Hull p) := by
    rw [invTRootE, ValuativeExtension.vle_iff_vle (A := Hull p) (B := Extension p)]
    exact ValuativeRel.not_vle.mpr (one_vlt_invTRoot p)
  simpa using (ValuativeRel.not_vle.mp h)

theorem root_sub_eq_invTRootE_pow :
    (asRoot p) ^ p - asRoot p = (invTRootE p) ^ p := by
  rw [asRoot, invTRootE_pow, ArtinSchreierDefect.root_equation]

theorem asRoot_veq_invTRootE : asRoot p =ᵥ invTRootE p := by
  let v := spectralValuation p (Extension p)
  have heq : (asRoot p) ^ p - asRoot p = (invTRootE p) ^ p :=
    root_sub_eq_invTRootE_pow p
  have hσ1 : 1 < v (invTRootE p) := by
    have := (Valuation.vlt_iff_lt (v := v)).mp (one_vlt_invTRootE p)
    rwa [map_one v] at this
  have hσp : 1 < v ((invTRootE p) ^ p) := by
    rw [map_pow]
    exact lt_trans hσ1 (lt_self_pow₀ hσ1 (Fact.out : p.Prime).one_lt)
  have hα1 : 1 < v (asRoot p) := by
    by_contra h
    have hle : v (asRoot p) ≤ 1 := le_of_not_gt h
    have hpow : v ((asRoot p) ^ p) ≤ 1 := by
      rw [map_pow]
      exact pow_le_one₀ bot_le hle
    have hsub : v ((asRoot p) ^ p - asRoot p) ≤ 1 := v.map_sub_le hpow hle
    rw [heq] at hsub
    exact (not_le_of_gt hσp) hsub
  have hlt : v (asRoot p) < v ((asRoot p) ^ p) := by
    rw [map_pow]
    exact lt_self_pow₀ hα1 (Fact.out : p.Prime).one_lt
  have hpows : v (asRoot p) ^ p = v (invTRootE p) ^ p := by
    rw [← map_pow, ← v.map_sub_eq_of_lt_left hlt, heq, map_pow]
  exact (Valuation.veq_iff_eq (v := v)).mpr
    ((pow_left_inj₀ bot_le bot_le (Fact.out : p.Prime).ne_zero).mp hpows)

noncomputable def unitGen : Extension p := asRoot p / invTRootE p

theorem unitGen_mul_invTRootE : unitGen p * invTRootE p = asRoot p :=
  div_mul_cancel₀ (asRoot p) (invTRootE_ne_zero p)

theorem unitGen_veq_one : unitGen p =ᵥ (1 : Extension p) := by
  let v := spectralValuation p (Extension p)
  have hv : v (asRoot p) = v (invTRootE p) :=
    (Valuation.veq_iff_eq (v := v)).mp (asRoot_veq_invTRootE p)
  have hσ0 : v (invTRootE p) ≠ 0 :=
    (Valuation.ne_zero_iff v).mpr (invTRootE_ne_zero p)
  have : v (unitGen p) = v 1 := by
    simp [unitGen, map_div₀, hv, div_self hσ0, map_one]
  exact (Valuation.veq_iff_eq (v := v)).mpr this

theorem unitGen_pow_sub_one :
    (unitGen p) ^ p - 1 = unitGen p / (invTRootE p) ^ (p - 1) := by
  have hσ : invTRootE p ≠ 0 := invTRootE_ne_zero p
  have h : (unitGen p * invTRootE p) ^ p - unitGen p * invTRootE p =
      (invTRootE p) ^ p := by
    rw [unitGen_mul_invTRootE, root_sub_eq_invTRootE_pow]
  rw [mul_pow] at h
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  apply (eq_div_iff (pow_ne_zero _ hσ)).mpr
  apply mul_right_cancel₀ hσ
  calc
    (((unitGen p) ^ p - 1) * (invTRootE p) ^ (p - 1)) * invTRootE p
        = ((unitGen p) ^ p - 1) * (invTRootE p) ^ p := by
          rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hp1]
    _ = unitGen p * invTRootE p := by linear_combination h

theorem unitGen_sub_one_pow :
    (unitGen p - 1) ^ p = unitGen p / (invTRootE p) ^ (p - 1) := by
  rw [sub_pow_char, one_pow, unitGen_pow_sub_one]

theorem unitGen_sub_one_vlt_one : unitGen p - 1 <ᵥ (1 : Extension p) := by
  let v := spectralValuation p (Extension p)
  have hpow : (unitGen p - 1) ^ p =
      unitGen p / (invTRootE p) ^ (p - 1) := unitGen_sub_one_pow p
  have hv1 : v (unitGen p) = 1 := by
    have := (Valuation.veq_iff_eq (v := v)).mp (unitGen_veq_one p)
    rwa [map_one v] at this
  have hσ1 : 1 < v (invTRootE p) := by
    have := (Valuation.vlt_iff_lt (v := v)).mp (one_vlt_invTRootE p)
    rwa [map_one v] at this
  have hpred0 : p - 1 ≠ 0 :=
    (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt).ne'
  have hden1 : 1 < v ((invTRootE p) ^ (p - 1)) := by
    rw [map_pow]
    exact one_lt_pow₀ hσ1 hpred0
  have hright : v (unitGen p / (invTRootE p) ^ (p - 1)) < 1 := by
    have hσ0 : v ((invTRootE p) ^ (p - 1)) ≠ 0 :=
      (Valuation.ne_zero_iff v).mpr (pow_ne_zero _ (invTRootE_ne_zero p))
    rw [map_div₀, hv1, one_div]
    exact inv_lt_one_iff₀.mpr (Or.inr hden1)
  have hpval : v ((unitGen p - 1) ^ p) < 1 := by simpa [hpow] using hright
  have hlt : v (unitGen p - 1) < v 1 := by
    have : v (unitGen p - 1) < 1 :=
      lt_of_pow_lt_pow_left₀ p bot_le (by simpa [map_pow] using hpval)
    rwa [map_one v]
  exact (Valuation.vlt_iff_lt (v := v)).mpr hlt

theorem veq_of_algebraMap_base {x y : Base p}
    (h : algebraMap (Base p) (Hull p) x =ᵥ algebraMap (Base p) (Hull p) y) : x =ᵥ y :=
  ⟨(ValuativeExtension.vle_iff_vle (A := Base p) (B := Hull p) x y).mp h.1,
    (ValuativeExtension.vle_iff_vle (A := Base p) (B := Hull p) y x).mp h.2⟩

theorem veq_of_algebraMap_hull {x y : Hull p}
    (h : algebraMap (Hull p) (Extension p) x =ᵥ algebraMap (Hull p) (Extension p) y) :
    x =ᵥ y :=
  ⟨(ValuativeExtension.vle_iff_vle (A := Hull p) (B := Extension p) x y).mp h.1,
    (ValuativeExtension.vle_iff_vle (A := Hull p) (B := Extension p) y x).mp h.2⟩

theorem not_pth_veq_inverseT_pow (x : Base p) (m : ℕ) (hm : ¬ p ∣ m) :
    ¬ x ^ p =ᵥ (inverseT p) ^ m := by
  intro h
  have hv := (Valuation.veq_iff_eq
    (v := (Valued.v : Valuation (Base p) ℤᵐ⁰))).mp h
  have hval : (Valued.v x) ^ p = WithZero.exp (m : ℤ) := by
    calc
      (Valued.v x) ^ p = Valued.v (x ^ p) := by rw [map_pow]
      _ = Valued.v ((inverseT p) ^ m) := hv
      _ = (WithZero.exp (1 : ℤ)) ^ m := by rw [map_pow, ArtinSchreierDefect.inverseT_value]
      _ = WithZero.exp (m : ℤ) := by rw [← WithZero.exp_nsmul]; simp
  have hh := congrArg WithZero.log hval
  have hh' : (p : ℤ) * WithZero.log (Valued.v x) = (m : ℤ) := by
    simpa [WithZero.log_pow] using hh
  apply hm
  rw [← Int.natCast_dvd_natCast]
  exact ⟨WithZero.log (Valued.v x), hh'.symm⟩

theorem not_veq_unitGen_sub_one_pow_of_levelOne {h : Hull p}
    (hh : IsLevelOne p h) (hnz : h ≠ 0) {k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    ¬ algebraMap (Hull p) (Extension p) h =ᵥ (unitGen p - 1) ^ k := by
  intro heq
  obtain ⟨b, hb⟩ := hh
  have hb0 : b ≠ 0 := by
    intro hbz
    rw [hbz, map_zero] at hb
    exact hnz ((pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).mp hb)
  let v := spectralValuation p (Extension p)
  have hv : v (algebraMap (Hull p) (Extension p) h) =
      v ((unitGen p - 1) ^ k) :=
    (Valuation.veq_iff_eq (v := v)).mp heq
  have hv1 : v (unitGen p) = 1 := by
    have := (Valuation.veq_iff_eq (v := v)).mp (unitGen_veq_one p)
    rwa [map_one v] at this
  have hβp : v ((unitGen p - 1) ^ p) =
      (v (invTRootE p))⁻¹ ^ (p - 1) := by
    rw [unitGen_sub_one_pow, map_div₀, hv1, one_div, map_pow, inv_pow]
  have hleft : v (algebraMap (Hull p) (Extension p) ((h⁻¹) ^ (p * p))) =
      v (algebraMap (Hull p) (Extension p)
        (algebraMap (Base p) (Hull p) ((inverseT p) ^ ((p - 1) * k)))) := by
    have hvh : v (algebraMap (Hull p) (Extension p) h) ^ (p * p) =
        (v (invTRootE p))⁻¹ ^ ((p - 1) * k * p) := by
      calc
        v (algebraMap (Hull p) (Extension p) h) ^ (p * p)
            = v ((unitGen p - 1) ^ k) ^ (p * p) := by rw [hv]
        _ = v (unitGen p - 1) ^ (k * (p * p)) := by rw [map_pow, ← pow_mul]
        _ = (v (unitGen p - 1) ^ p) ^ (k * p) := by
          rw [← pow_mul]
          congr 1
          ring
        _ = ((v (invTRootE p))⁻¹ ^ (p - 1)) ^ (k * p) := by
          rw [← map_pow, hβp]
        _ = (v (invTRootE p))⁻¹ ^ ((p - 1) * k * p) := by
          rw [← pow_mul]
          congr 1
          ring
    calc
      v (algebraMap (Hull p) (Extension p) ((h⁻¹) ^ (p * p)))
          = (v (algebraMap (Hull p) (Extension p) h) ^ (p * p))⁻¹ := by
            simp only [map_pow, map_inv₀, inv_pow]
      _ = v (invTRootE p) ^ ((p - 1) * k * p) := by
          rw [hvh]
          simp
      _ = (v (invTRootE p) ^ p) ^ ((p - 1) * k) := by
          rw [← pow_mul]
          congr 1
          ring
      _ = v ((invTRootE p) ^ p) ^ ((p - 1) * k) := by rw [map_pow]
      _ = v (algebraMap (Hull p) (Extension p)
            (algebraMap (Base p) (Hull p) (inverseT p))) ^ ((p - 1) * k) := by
          rw [invTRootE_pow]
      _ = v (algebraMap (Hull p) (Extension p)
            (algebraMap (Base p) (Hull p) ((inverseT p) ^ ((p - 1) * k)))) := by
          simp [map_pow]
  have heqE : algebraMap (Hull p) (Extension p) ((h⁻¹) ^ (p * p)) =ᵥ
      algebraMap (Hull p) (Extension p)
        (algebraMap (Base p) (Hull p) ((inverseT p) ^ ((p - 1) * k))) :=
    (Valuation.veq_iff_eq (v := v)).mpr hleft
  have hbaseE : algebraMap (Base p) (Hull p) ((b⁻¹) ^ p) =ᵥ
      algebraMap (Base p) (Hull p) ((inverseT p) ^ ((p - 1) * k)) := by
    apply veq_of_algebraMap_hull p
    have hinvpow : (h⁻¹) ^ (p * p) =
        algebraMap (Base p) (Hull p) ((b⁻¹) ^ p) := by
      rw [pow_mul, inv_pow, hb]
      simp
    simpa [hinvpow] using heqE
  have hbase : (b⁻¹) ^ p =ᵥ (inverseT p) ^ ((p - 1) * k) :=
    veq_of_algebraMap_base p hbaseE
  have hpdvd : ¬ p ∣ (p - 1) * k := by
    intro hdvd
    rcases (Fact.out : p.Prime).dvd_mul.mp hdvd with hdvd | hdvd
    · exact (Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
        (Nat.sub_lt (Fact.out : p.Prime).pos Nat.one_pos)) hdvd
    · exact (Nat.not_dvd_of_pos_of_lt hk0 hkp) hdvd
  exact not_pth_veq_inverseT_pow p b⁻¹ ((p - 1) * k) hpdvd hbase

theorem isLevelOne_finset_sum {I : Type*} {s : Finset I} {f : I → Hull p}
    (hf : ∀ i ∈ s, IsLevelOne p (f i)) : IsLevelOne p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isLevelOne_zero p
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact isLevelOne_add p (hf a (by simp)) (ih (by
        intro i hi
        exact hf i (by simp [hi])))

/-- Every coefficient of the polynomial lies in the first purely inseparable layer. -/
def IsLevelOneCoeffs (q : (Hull p)[X]) : Prop :=
  ∀ n, IsLevelOne p (q.coeff n)

theorem isLevelOneCoeffs_zero : IsLevelOneCoeffs p 0 := by
  intro n
  simp only [coeff_zero]
  exact isLevelOne_zero p

theorem isLevelOneCoeffs_C {a : Hull p} (ha : IsLevelOne p a) :
    IsLevelOneCoeffs p (C a) := by
  intro n
  by_cases hn : n = 0
  · simpa [hn] using ha
  · simp [coeff_C, hn, isLevelOne_zero p]

theorem isLevelOneCoeffs_X : IsLevelOneCoeffs p (X : (Hull p)[X]) := by
  intro n
  simp only [coeff_X]
  split
  · exact isLevelOne_one p
  · exact isLevelOne_zero p

theorem isLevelOneCoeffs_add {q r : (Hull p)[X]}
    (hq : IsLevelOneCoeffs p q) (hr : IsLevelOneCoeffs p r) :
    IsLevelOneCoeffs p (q + r) := by
  intro n
  rw [coeff_add]
  exact isLevelOne_add p (hq n) (hr n)

theorem isLevelOneCoeffs_mul {q r : (Hull p)[X]}
    (hq : IsLevelOneCoeffs p q) (hr : IsLevelOneCoeffs p r) :
    IsLevelOneCoeffs p (q * r) := by
  intro n
  rw [coeff_mul]
  apply isLevelOne_finset_sum p
  intro ij hij
  exact isLevelOne_mul p (hq ij.1) (hr ij.2)

theorem isLevelOneCoeffs_pow {q : (Hull p)[X]} (hq : IsLevelOneCoeffs p q) (n : ℕ) :
    IsLevelOneCoeffs p (q ^ n) := by
  induction n with
  | zero => simpa using isLevelOneCoeffs_C p (isLevelOne_one p)
  | succ n ih =>
      rw [pow_succ]
      exact isLevelOneCoeffs_mul p ih hq

theorem isLevelOneCoeffs_finset_sum {I : Type*} {s : Finset I}
    {f : I → (Hull p)[X]} (hf : ∀ i ∈ s, IsLevelOneCoeffs p (f i)) :
    IsLevelOneCoeffs p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isLevelOneCoeffs_zero p
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact isLevelOneCoeffs_add p (hf a (by simp)) (ih (by
        intro i hi
        exact hf i (by simp [hi])))

theorem isLevelOneCoeffs_comp {q r : (Hull p)[X]}
    (hq : IsLevelOneCoeffs p q) (hr : IsLevelOneCoeffs p r) :
    IsLevelOneCoeffs p (q.comp r) := by
  rw [← q.sum_C_mul_X_pow_eq] at ⊢
  rw [sum_def, sum_comp]
  apply isLevelOneCoeffs_finset_sum p
  intro n hn
  rw [C_mul_X_pow_eq_monomial, monomial_comp]
  exact isLevelOneCoeffs_mul p (isLevelOneCoeffs_C p (hq n))
    (isLevelOneCoeffs_pow p hr n)

theorem exists_root_polynomial_coords (x : Extension p) :
    ∃ q : (Hull p)[X], q.natDegree < p ∧
      x = eval₂ (algebraMap (Hull p) (Extension p)) (asRoot p) q := by
  have hmonic : (standardPolynomial p).Monic :=
    ArtinSchreier.monic p (algebraMap (Base p) (Hull p) (inverseT p))
  obtain ⟨g, hg⟩ := (AdjoinRoot.mk_surjective (g := standardPolynomial p)) x
  let q := g %ₘ standardPolynomial p
  have hqmk : AdjoinRoot.mk (standardPolynomial p) q =
      AdjoinRoot.mk (standardPolynomial p) g := by
    rw [AdjoinRoot.mk_eq_mk]
    have hrem := modByMonic_eq_sub_mul_div g (standardPolynomial p)
    change standardPolynomial p ∣ (g %ₘ standardPolynomial p) - g
    rw [hrem]
    have hdiff : (g - standardPolynomial p * (g /ₘ standardPolynomial p)) - g =
        - (standardPolynomial p * (g /ₘ standardPolynomial p)) := by ring
    rw [hdiff]
    exact dvd_neg.mpr (dvd_mul_right _ _)
  have hdegf : (standardPolynomial p).degree = p := by
    have hnat : (standardPolynomial p).natDegree = p :=
      ArtinSchreier.natDegree_polynomial p _
    rw [degree_eq_natDegree hmonic.ne_zero, hnat]
  have hqdeg : q.natDegree < p := by
    rcases eq_or_ne q 0 with hq0 | hq0
    · simp [hq0, (Fact.out : p.Prime).pos]
    · rw [natDegree_lt_iff_degree_lt hq0]
      simpa [hdegf] using degree_modByMonic_lt g hmonic
  refine ⟨q, hqdeg, ?_⟩
  rw [← hg, ← hqmk]
  simp only [asRoot, ← aeval_def, AdjoinRoot.aeval_eq]

theorem isLevelOne_pow_lift {x : Hull p} {m n : ℕ}
    (hx : IsLevelOne p (x ^ (p ^ m))) (hmn : m ≤ n) :
    IsLevelOne p (x ^ (p ^ n)) := by
  have hpow : p ^ n = p ^ m * p ^ (n - m) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hmn]
  rw [show x ^ (p ^ n) = (x ^ (p ^ m)) ^ (p ^ (n - m)) by rw [hpow, pow_mul]]
  exact isLevelOne_pow p hx _

theorem exists_common_pow_levelOne {I : Type*} (s : Finset I) (f : I → Hull p) :
    ∃ n : ℕ, ∀ i ∈ s, IsLevelOne p (f i ^ (p ^ n)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨na, ya, hya⟩ := exists_pow_in_base p (f a)
      obtain ⟨ns, hs⟩ := ih
      refine ⟨max na ns, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · apply isLevelOne_pow_lift p (m := na) (n := max na ns) _ (Nat.le_max_left _ _)
        rw [hya]
        exact isLevelOne_algebraMap p ya
      · exact isLevelOne_pow_lift p (hs i hi) (Nat.le_max_right _ _)

theorem exists_asRoot_pow_translate (n : ℕ) :
    ∃ b : Base p, (asRoot p) ^ (p ^ n) = asRoot p +
      algebraMap (Hull p) (Extension p) (algebraMap (Base p) (Hull p) b) := by
  induction n with
  | zero =>
      refine ⟨0, ?_⟩
      simp
  | succ n ih =>
      obtain ⟨b, hb⟩ := ih
      refine ⟨inverseT p + b ^ p, ?_⟩
      have hroot : (asRoot p) ^ p = asRoot p +
          algebraMap (Hull p) (Extension p)
            (algebraMap (Base p) (Hull p) (inverseT p)) := by
        calc
          (asRoot p) ^ p = ((asRoot p) ^ p - asRoot p) + asRoot p := by ring
          _ = algebraMap (Hull p) (Extension p)
                (algebraMap (Base p) (Hull p) (inverseT p)) + asRoot p := by
              rw [root_sub_eq_invTRootE_pow, invTRootE_pow]
          _ = asRoot p + algebraMap (Hull p) (Extension p)
                (algebraMap (Base p) (Hull p) (inverseT p)) := by ring
      calc
        (asRoot p) ^ (p ^ (n + 1)) = ((asRoot p) ^ (p ^ n)) ^ p := by
          rw [Nat.pow_succ, pow_mul]
        _ = (asRoot p + algebraMap (Hull p) (Extension p)
              (algebraMap (Base p) (Hull p) b)) ^ p := by rw [hb]
        _ = (asRoot p) ^ p + (algebraMap (Hull p) (Extension p)
              (algebraMap (Base p) (Hull p) b)) ^ p := by
            rw [add_pow_char (p := p)]
        _ = asRoot p + algebraMap (Hull p) (Extension p)
              (algebraMap (Base p) (Hull p) (inverseT p + b ^ p)) := by
            rw [hroot]
            simp only [map_add, map_pow]
            abel

theorem natDegree_finset_sum_lt {I : Type*} {s : Finset I}
    {f : I → (Hull p)[X]} (hf : ∀ i ∈ s, (f i).natDegree < p) :
    (∑ i ∈ s, f i).natDegree < p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Fact.out : p.Prime).pos
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact lt_of_le_of_lt (natDegree_add_le _ _)
        (max_lt (hf a (by simp)) (ih (by
          intro i hi
          exact hf i (by simp [hi]))))

theorem exists_levelOne_pow_polynomial (x : Extension p) :
    ∃ n : ℕ, ∃ s : (Hull p)[X], s.natDegree < p ∧ IsLevelOneCoeffs p s ∧
      x ^ (p ^ n) = eval₂ (algebraMap (Hull p) (Extension p))
        (unitGen p - 1) s := by
  classical
  obtain ⟨q, hqdeg, hx⟩ := exists_root_polynomial_coords p x
  obtain ⟨n, hn⟩ := exists_common_pow_levelOne p q.support q.coeff
  let e := p ^ n
  let qF : (Hull p)[X] := q.sum fun i a ↦ C (a ^ e) * X ^ i
  have hqFlevel : IsLevelOneCoeffs p qF := by
    dsimp [qF]
    rw [sum_def]
    apply isLevelOneCoeffs_finset_sum p
    intro i hi
    exact isLevelOneCoeffs_mul p (isLevelOneCoeffs_C p (hn i hi))
      (isLevelOneCoeffs_pow p (isLevelOneCoeffs_X p) i)
  have hqFdeg : qF.natDegree < p := by
    dsimp [qF]
    rw [sum_def]
    apply natDegree_finset_sum_lt p
    intro i hi
    have hiq : i ≤ q.natDegree :=
      le_natDegree_of_ne_zero (mem_support_iff.mp hi)
    calc
      (C (q.coeff i ^ e) * X ^ i).natDegree
          ≤ (C (q.coeff i ^ e)).natDegree + (X ^ i).natDegree := natDegree_mul_le
      _ = i := by simp
      _ < p := lt_of_le_of_lt hiq hqdeg
  have hxpow : x ^ e = eval₂ (algebraMap (Hull p) (Extension p))
      ((asRoot p) ^ e) qF := by
    rw [hx, eval₂_eq_sum, sum_def, sum_pow_char_pow p n]
    dsimp [qF]
    rw [eval₂_sum, sum_def]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, map_pow, mul_pow]
    change (algebraMap (Hull p) (Extension p) (q.coeff i)) ^ e *
        ((asRoot p) ^ i) ^ e =
      (algebraMap (Hull p) (Extension p) (q.coeff i)) ^ e *
        ((asRoot p) ^ e) ^ i
    congr 1
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  obtain ⟨b, hb⟩ := exists_asRoot_pow_translate p n
  let translate : (Hull p)[X] :=
    X + C (algebraMap (Base p) (Hull p) b)
  let r : (Hull p)[X] := qF.comp translate
  have htranslate_level : IsLevelOneCoeffs p translate :=
    isLevelOneCoeffs_add p (isLevelOneCoeffs_X p)
      (isLevelOneCoeffs_C p (isLevelOne_algebraMap p b))
  have htranslate_deg : translate.natDegree = 1 := by
    simp [translate]
  have hrlevel : IsLevelOneCoeffs p r :=
    isLevelOneCoeffs_comp p hqFlevel htranslate_level
  have hrdeg : r.natDegree < p := by
    apply lt_of_le_of_lt natDegree_comp_le
    simpa [r, htranslate_deg] using hqFdeg
  have hxroot : x ^ e = eval₂ (algebraMap (Hull p) (Extension p)) (asRoot p) r := by
    rw [hxpow]
    change eval₂ (algebraMap (Hull p) (Extension p)) ((asRoot p) ^ e) qF =
      eval₂ (algebraMap (Hull p) (Extension p)) (asRoot p) (qF.comp translate)
    rw [eval₂_comp]
    simp only [translate, eval₂_add, eval₂_X, eval₂_C]
    rw [hb]
  let scaleShift : (Hull p)[X] :=
    C (invTRoot p) * (X + C 1)
  let s : (Hull p)[X] := r.comp scaleShift
  have hscale_level : IsLevelOneCoeffs p scaleShift :=
    isLevelOneCoeffs_mul p (isLevelOneCoeffs_C p (isLevelOne_invTRoot p))
      (isLevelOneCoeffs_add p (isLevelOneCoeffs_X p)
        (isLevelOneCoeffs_C p (isLevelOne_one p)))
  have hscale_deg : scaleShift.natDegree = 1 := by
    dsimp [scaleShift]
    rw [natDegree_C_mul (invTRoot_ne_zero p), natDegree_X_add_C]
  have hslevel : IsLevelOneCoeffs p s :=
    isLevelOneCoeffs_comp p hrlevel hscale_level
  have hsdeg : s.natDegree < p := by
    apply lt_of_le_of_lt natDegree_comp_le
    simpa [s, hscale_deg] using hrdeg
  refine ⟨n, s, hsdeg, hslevel, ?_⟩
  rw [hxroot]
  have hscale_eval : eval₂ (algebraMap (Hull p) (Extension p))
      (unitGen p - 1) scaleShift = asRoot p := by
    simp only [scaleShift, eval₂_mul, eval₂_C, eval₂_add, eval₂_X]
    rw [map_one, sub_add_cancel, mul_comm]
    change unitGen p * invTRootE p = asRoot p
    exact unitGen_mul_invTRootE p
  dsimp [s]
  conv_rhs => rw [eval₂_comp]
  change eval₂ (algebraMap (Hull p) (Extension p)) (asRoot p) r =
    eval₂ (algebraMap (Hull p) (Extension p))
      (eval₂ (algebraMap (Hull p) (Extension p)) (unitGen p - 1) scaleShift) r
  rw [hscale_eval]

theorem unitGen_ne_zero : unitGen p ≠ 0 := by
  intro hu
  have h := unitGen_veq_one p
  rw [hu, veq_zero_iff] at h
  exact zero_ne_one h

theorem unitGen_sub_one_ne_zero : unitGen p - 1 ≠ 0 := by
  intro hβ
  have hpow := unitGen_sub_one_pow p
  rw [hβ, zero_pow (Fact.out : p.Prime).ne_zero] at hpow
  have hdiv : unitGen p / (invTRootE p) ^ (p - 1) ≠ 0 :=
    div_ne_zero (unitGen_ne_zero p)
      (pow_ne_zero _ (invTRootE_ne_zero p))
  exact hdiv hpow.symm

/-- Distinct nonzero terms in a level-one expansion in powers of `unitGen - 1`
have distinct valuations. -/
theorem not_terms_veq_of_lt {a b : Hull p}
    (ha : IsLevelOne p a) (hb : IsLevelOne p b) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    {i j : ℕ} (hij : i < j) (hjp : j < p) :
    ¬ algebraMap (Hull p) (Extension p) a * (unitGen p - 1) ^ i =ᵥ
      algebraMap (Hull p) (Extension p) b * (unitGen p - 1) ^ j := by
  intro heq
  let v := spectralValuation p (Extension p)
  have hv := (Valuation.veq_iff_eq (v := v)).mp heq
  simp only [map_mul, map_pow] at hv
  have hβ0 : v (unitGen p - 1) ≠ 0 :=
    (Valuation.ne_zero_iff v).mpr (unitGen_sub_one_ne_zero p)
  have hbE0 : algebraMap (Hull p) (Extension p) b ≠ 0 :=
    by
      intro h
      exact hb0 ((algebraMap (Hull p) (Extension p)).injective (by simpa using h))
  have hvb0 : v (algebraMap (Hull p) (Extension p) b) ≠ 0 :=
    (Valuation.ne_zero_iff v).mpr hbE0
  have hcancel : v (algebraMap (Hull p) (Extension p) a) =
      v (algebraMap (Hull p) (Extension p) b) * v (unitGen p - 1) ^ (j - i) := by
    apply mul_left_cancel₀ (pow_ne_zero i hβ0)
    calc
      v (unitGen p - 1) ^ i * v (algebraMap (Hull p) (Extension p) a) =
          v (algebraMap (Hull p) (Extension p) a) * v (unitGen p - 1) ^ i :=
        mul_comm _ _
      _ = v (algebraMap (Hull p) (Extension p) b) *
          v (unitGen p - 1) ^ j := hv
      _ = v (unitGen p - 1) ^ i *
          (v (algebraMap (Hull p) (Extension p) b) *
            v (unitGen p - 1) ^ (j - i)) := by
        have hpj : v (unitGen p - 1) ^ j =
            v (unitGen p - 1) ^ i * v (unitGen p - 1) ^ (j - i) := by
          conv_lhs => rw [show j = i + (j - i) by omega, pow_add]
        rw [hpj]
        ac_rfl
  have hquotval : v (algebraMap (Hull p) (Extension p) (a * b⁻¹)) =
      v (unitGen p - 1) ^ (j - i) := by
    rw [map_mul, map_inv₀, map_mul, map_inv₀, hcancel]
    rw [mul_right_comm, mul_inv_cancel₀ hvb0, one_mul]
  have hquot : IsLevelOne p (a * b⁻¹) :=
    isLevelOne_mul p ha (isLevelOne_inv p hb)
  have hquot0 : a * b⁻¹ ≠ 0 := mul_ne_zero ha0 (inv_ne_zero hb0)
  apply not_veq_unitGen_sub_one_pow_of_levelOne p hquot hquot0
    (Nat.sub_pos_of_lt hij)
    (lt_of_le_of_lt (Nat.sub_le j i) hjp)
  exact (Valuation.veq_iff_eq (v := v)).mpr (by rw [map_pow]; exact hquotval)

theorem not_term_veq_one {a : Hull p} (ha : IsLevelOne p a) (ha0 : a ≠ 0)
    {i : ℕ} (hi0 : 0 < i) (hip : i < p) :
    ¬ algebraMap (Hull p) (Extension p) a * (unitGen p - 1) ^ i =ᵥ
      (1 : Extension p) := by
  intro heq
  let v := spectralValuation p (Extension p)
  have hv := (Valuation.veq_iff_eq (v := v)).mp heq
  simp only [map_mul, map_pow, map_one] at hv
  have haE0 : algebraMap (Hull p) (Extension p) a ≠ 0 := by
    intro h
    exact ha0 ((algebraMap (Hull p) (Extension p)).injective (by simpa using h))
  have hva0 : v (algebraMap (Hull p) (Extension p) a) ≠ 0 :=
    (Valuation.ne_zero_iff v).mpr haE0
  have hinvval : v (algebraMap (Hull p) (Extension p) a⁻¹) =
      v (unitGen p - 1) ^ i := by
    rw [map_inv₀, map_inv₀]
    exact inv_eq_of_mul_eq_one_right hv
  apply not_veq_unitGen_sub_one_pow_of_levelOne p (isLevelOne_inv p ha)
    (inv_ne_zero ha0) hi0 hip
  exact (Valuation.veq_iff_eq (v := v)).mpr (by rw [map_pow]; exact hinvval)

theorem vle_one_of_algebraMap {y : Hull p}
    (h : algebraMap (Hull p) (Extension p) y ≤ᵥ (1 : Extension p)) : y ≤ᵥ 1 := by
  have h' : algebraMap (Hull p) (Extension p) y ≤ᵥ
      algebraMap (Hull p) (Extension p) (1 : Hull p) := by simpa using h
  exact (ValuativeExtension.vle_iff_vle (A := Hull p) (B := Extension p) y 1).mp h'

/-- An integral level-one polynomial in `unitGen - 1` is congruent modulo the
maximal ideal to its constant coefficient. -/
theorem integral_levelOne_polynomial_cong {z : Extension p} {s : (Hull p)[X]}
    (hsdeg : s.natDegree < p) (hslevel : IsLevelOneCoeffs p s)
    (hz : z = eval₂ (algebraMap (Hull p) (Extension p)) (unitGen p - 1) s)
    (hint : z ≤ᵥ (1 : Extension p)) :
    ∃ y : Hull p, y ≤ᵥ 1 ∧ z - algebraMap (Hull p) (Extension p) y <ᵥ 1 := by
  classical
  let v := spectralValuation p (Extension p)
  let term : ℕ → Extension p := fun i ↦
    algebraMap (Hull p) (Extension p) (s.coeff i) * (unitGen p - 1) ^ i
  let indices := (Finset.range p).filter fun i ↦ s.coeff i ≠ 0
  have heval : z = ∑ i ∈ Finset.range p, term i := by
    rw [hz, eval₂_eq_sum_range' (algebraMap (Hull p) (Extension p)) hsdeg]
  have hfiltered : (∑ i ∈ indices, term i) = ∑ i ∈ Finset.range p, term i := by
    apply Finset.sum_filter_of_ne
    intro i hi hterm hcoeff
    apply hterm
    simp [term, hcoeff]
  by_cases hindices : indices.Nonempty
  · obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image indices (fun i ↦ v (term i)) hindices
    have hjrange : j ∈ Finset.range p := (Finset.mem_filter.mp hj).1
    have hjcoeff : s.coeff j ≠ 0 := (Finset.mem_filter.mp hj).2
    have hstrict : ∀ i ∈ indices \ {j}, v (term i) < v (term j) := by
      intro i hi
      have hiindices : i ∈ indices := (Finset.mem_sdiff.mp hi).1
      have hine : i ≠ j := by simpa using (Finset.mem_sdiff.mp hi).2
      have hirange : i ∈ Finset.range p := (Finset.mem_filter.mp hiindices).1
      have hicoeff : s.coeff i ≠ 0 := (Finset.mem_filter.mp hiindices).2
      apply lt_of_le_of_ne (hmax i hiindices)
      intro heq
      have hveq : term i =ᵥ term j := (Valuation.veq_iff_eq (v := v)).mpr heq
      rcases lt_or_gt_of_ne hine with hij | hji
      · exact not_terms_veq_of_lt p (hslevel i) (hslevel j) hicoeff hjcoeff hij
          (Finset.mem_range.mp hjrange) hveq
      · exact not_terms_veq_of_lt p (hslevel j) (hslevel i) hjcoeff hicoeff hji
          (Finset.mem_range.mp hirange) hveq.symm
    have hsumval : v (∑ i ∈ indices, term i) = v (term j) :=
      v.map_sum_eq_of_lt hj hstrict
    have hzval : v z = v (term j) := by
      rw [heval, ← hfiltered, hsumval]
    have hzle : v z ≤ 1 := by
      have := (Valuation.vle_iff_le (v := v)).mp hint
      rwa [map_one v] at this
    have htermle : ∀ i ∈ Finset.range p, v (term i) ≤ 1 := by
      intro i hi
      by_cases hcoeff : s.coeff i = 0
      · simp [term, hcoeff]
      · exact le_trans (hmax i (Finset.mem_filter.mpr ⟨hi, hcoeff⟩))
          (hzval ▸ hzle)
    have hzero : 0 ∈ Finset.range p := by
      exact Finset.mem_range.mpr (Fact.out : p.Prime).pos
    have hconstleE : algebraMap (Hull p) (Extension p) (s.coeff 0) ≤ᵥ
        (1 : Extension p) := by
      apply (Valuation.vle_iff_le (v := v)).mpr
      simpa [term] using htermle 0 hzero
    refine ⟨s.coeff 0, vle_one_of_algebraMap p hconstleE, ?_⟩
    have hnonconst : ∀ i ∈ (Finset.range p).erase 0, v (term i) < 1 := by
      intro i hi
      have hirange : i ∈ Finset.range p := (Finset.mem_erase.mp hi).2
      have hi0 : 0 < i := Nat.pos_of_ne_zero (by
        intro hieq
        subst i
        exact (Finset.mem_erase.mp hi).1 rfl)
      by_cases hcoeff : s.coeff i = 0
      · simp [term, hcoeff]
      · apply lt_of_le_of_ne (htermle i hirange)
        intro heq
        apply not_term_veq_one p (hslevel i) hcoeff hi0 (Finset.mem_range.mp hirange)
        apply (Valuation.veq_iff_eq (v := v)).mpr
        change v (term i) = v (1 : Extension p)
        rw [map_one]
        exact heq
    have hdiff : z - algebraMap (Hull p) (Extension p) (s.coeff 0) =
        ∑ i ∈ (Finset.range p).erase 0, term i := by
      rw [heval, ← Finset.sum_erase_add _ _ hzero]
      simp [term]
    apply (Valuation.vlt_iff_lt (v := v)).mpr
    rw [hdiff, map_one]
    exact v.map_sum_lt one_ne_zero hnonconst
  · have hempty : indices = ∅ := Finset.not_nonempty_iff_eq_empty.mp hindices
    have hsumzero : (∑ i ∈ Finset.range p, term i) = 0 := by
      rw [← hfiltered, hempty]
      simp
    have hz0 : z = 0 := heval.trans hsumzero
    refine ⟨0, ?_, ?_⟩
    · apply (Valuation.vle_iff_le (v := spectralValuation p (Hull p))).mpr
      simp
    · apply (Valuation.vlt_iff_lt (v := v)).mpr
      simp [hz0]

theorem exists_pow_root_of_perfect {F : Type*} [Field F] [CharP F p] [PerfectField F]
    (n : ℕ) (a : F) : ∃ b : F, b ^ (p ^ n) = a := by
  induction n with
  | zero => exact ⟨a, by simp⟩
  | succ n ih =>
      obtain ⟨c, hc⟩ := ih
      obtain ⟨b, hb⟩ := surjective_frobenius F p c
      refine ⟨b, ?_⟩
      have hb' : b ^ p = c := by
        rw [← frobenius_def (R := F) (p := p)]
        exact hb
      rw [Nat.pow_succ, mul_comm, pow_mul, hb', hc]

instance hullIntegerCharP : CharP ↥𝒪[Hull p] p :=
  CharP.subring (Hull p) p (Valuation.integer (valuation (Hull p)))

instance extensionIntegerCharP : CharP ↥𝒪[Extension p] p :=
  CharP.subring (Extension p) p (Valuation.integer (valuation (Extension p)))

lemma residueCharP_of_charP (K : Type*) [Field K] [CharP K p] [ValuativeRel K] :
    CharP 𝓀[K] p := by
  let _ : CharP ↥𝒪[K] p :=
    CharP.subring K p (Valuation.integer (valuation K))
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
  rw [← map_natCast (IsLocalRing.residue ↥𝒪[K]) p, CharP.cast_eq_zero]
  exact map_zero _

instance hullResidueCharP : CharP 𝓀[Hull p] p :=
  residueCharP_of_charP p (Hull p)

instance extensionResidueCharP : CharP 𝓀[Extension p] p :=
  residueCharP_of_charP p (Extension p)

instance hullResiduePerfect : PerfectField 𝓀[Hull p] := by
  have : ExpChar 𝓀[Hull p] p := inferInstance
  have : PerfectRing 𝓀[Hull p] p := by
    refine PerfectRing.ofSurjective 𝓀[Hull p] p ?_
    intro a
    obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (I := 𝓂[Hull p]) a
    obtain ⟨y, hy⟩ := surjective_frobenius (Hull p) p (u : Hull p)
    have hu1 : (u : Hull p) ≤ᵥ 1 :=
      (Valuation.vle_one_iff (v := valuation (Hull p))).mpr
        ((Valuation.mem_integer_iff (valuation (Hull p)) (u : Hull p)).mp u.property)
    have hyp : y ^ p = (u : Hull p) := by
      rw [← frobenius_def (R := Hull p) (p := p)]
      exact hy
    have hyi : y ≤ᵥ (1 : Hull p) :=
      (ArtinSchreierDefect.General.pow_vle_pow_iff
        (Hull p) y 1 p (Fact.out : p.Prime).ne_zero).mp
        (by simpa [hyp, one_pow] using hu1)
    let yO : 𝒪[Hull p] :=
      ⟨y, (Valuation.mem_integer_iff (valuation (Hull p)) y).mpr
        ((Valuation.vle_one_iff (v := valuation (Hull p))).mp hyi)⟩
    refine ⟨IsLocalRing.residue 𝒪[Hull p] yO, ?_⟩
    change (IsLocalRing.residue 𝒪[Hull p] yO) ^ p = a
    rw [← hu, ← map_pow]
    congr 1
    exact Subtype.ext (by
      change y ^ p = (u : Hull p)
      exact hyp)
  exact PerfectRing.toPerfectField 𝓀[Hull p] p

/-- The residue degree of the Artin--Schreier defect extension is one for every prime. -/
theorem concrete_residueDegree : residueDegree (Hull p) (Extension p) = 1 := by
  refine residueDegree_eq_one_iff.mpr ?_
  intro z
  obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective (I := 𝓂[Extension p]) z
  set x : Extension p := (u : Extension p)
  have hint : x ≤ᵥ 1 :=
    (Valuation.vle_one_iff (v := valuation (Extension p))).mpr
      ((Valuation.mem_integer_iff (valuation (Extension p)) x).mp u.property)
  obtain ⟨n, s, hsdeg, hslevel, hpow⟩ := exists_levelOne_pow_polynomial p x
  have hpow_int : x ^ (p ^ n) ≤ᵥ 1 := by
    have := pow_vle_pow hint (p ^ n)
    simpa using this
  obtain ⟨y, hyint, hydiff⟩ :=
    integral_levelOne_polynomial_cong p hsdeg hslevel hpow hpow_int
  let yO : 𝒪[Hull p] :=
    ⟨y, (Valuation.mem_integer_iff (valuation (Hull p)) y).mpr
      ((Valuation.vle_one_iff (v := valuation (Hull p))).mp hyint)⟩
  let wO : 𝒪[Extension p] := u ^ (p ^ n)
  have hcongr : IsLocalRing.residue 𝒪[Extension p] wO =
      algebraMap 𝓀[Hull p] 𝓀[Extension p] (IsLocalRing.residue 𝒪[Hull p] yO) := by
    rw [IsLocalRing.ResidueField.algebraMap_residue]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    have hcoe : ((wO - algebraMap 𝒪[Hull p] 𝒪[Extension p] yO : 𝒪[Extension p]) :
        Extension p) = x ^ (p ^ n) - algebraMap (Hull p) (Extension p) y := by
      simp [wO, x, yO]
    have : valuation (Extension p)
        ((wO - algebraMap 𝒪[Hull p] 𝒪[Extension p] yO : 𝒪[Extension p]) :
          Extension p) < 1 := by
      have := (Valuation.vlt_iff_lt (v := valuation (Extension p))).mp hydiff
      simpa [hcoe] using this
    exact this
  have hroot : (IsLocalRing.residue 𝒪[Extension p] u) ^ (p ^ n) =
      algebraMap 𝓀[Hull p] 𝓀[Extension p] (IsLocalRing.residue 𝒪[Hull p] yO) := by
    simpa [wO] using hcongr
  obtain ⟨t, ht⟩ := exists_pow_root_of_perfect p n (IsLocalRing.residue 𝒪[Hull p] yO)
  refine ⟨t, ?_⟩
  have hsub : (IsLocalRing.residue 𝒪[Extension p] u -
      algebraMap 𝓀[Hull p] 𝓀[Extension p] t) ^ (p ^ n) = 0 := by
    rw [sub_pow_expChar_pow (p := p), hroot, ← map_pow, ht, sub_self]
  have hsubz : (algebraMap 𝓀[Hull p] 𝓀[Extension p] t - z) ^ (p ^ n) = 0 := by
    have hzres : z = IsLocalRing.residue 𝒪[Extension p] u := hu.symm
    rw [hzres]
    have hneg : algebraMap 𝓀[Hull p] 𝓀[Extension p] t -
        IsLocalRing.residue 𝒪[Extension p] u =
        -(IsLocalRing.residue 𝒪[Extension p] u -
          algebraMap 𝓀[Hull p] 𝓀[Extension p] t) := by ring
    rw [hneg]
    rw [neg_pow, hsub, mul_zero]
  exact eq_of_sub_eq_zero ((pow_eq_zero_iff (pow_ne_zero n
    (Fact.out : p.Prime).ne_zero)).mp hsubz)

/-- The Ostrowski sum is one, strictly below the prime extension degree. -/
theorem sum_strict :
    let := extensionFintype_of_unique (Hull p) (Extension p) (extension_eq_spectral p)
    (∑ w : Extensions (Hull p) (Extension p), extensionWeight w) =
      ramificationIndex (Hull p) (Extension p) * residueDegree (Hull p) (Extension p) ∧
    ramificationIndex (Hull p) (Extension p) * residueDegree (Hull p) (Extension p) = 1 ∧
    (∑ w : Extensions (Hull p) (Extension p), extensionWeight w) < p ∧
    p = Module.finrank (Hull p) (Extension p) := by
  let := extensionFintype_of_unique (Hull p) (Extension p) (extension_eq_spectral p)
  exact sum_strict_of_unique_immediate (Hull p) (Extension p) (extension_eq_spectral p) p
    (Fact.out : p.Prime).one_lt (concrete_ramificationIndex p) (concrete_residueDegree p)
    (ArtinSchreierDefect.extension_degree p)

end ArtinSchreierDefect.General
