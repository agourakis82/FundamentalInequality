/-
Copyright (c) 2026 Demetrios Chiuratto Agourakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Demetrios Chiuratto Agourakis
-/
module

public import Examples.ArtinSchreierDefect.Basic
public import Examples.Bridge.Completeness
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.RingTheory.Valuation.RankOne
public import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Spectral valuations and uniqueness for Artin–Schreier defect extensions

Compatible spectral valuations are constructed from Mathlib's spectral norm
over the complete Laurent series field. The ramification index of the
constructed valuation is one. Uniqueness of a compatible valuative relation
on the degree-`p` extension is deduced from completeness of `F_p((t))` and
`spectralNorm_unique_field_norm_ext`, after lifting rank at most one along
the finite extension of the hull. Compatibility along the tower uses
`ValuativeExtension.comp`. No general henselian uniqueness theorem is used,
and no `sorry` is introduced.
-/

@[expose] public section

noncomputable section

open Polynomial ValuativeRel ValuativeExtension
open scoped LaurentSeries WithZero ValuativeRel NNReal

namespace ArtinSchreierDefect.General

variable (p : ℕ) [Fact p.Prime]

abbrev Base := ArtinSchreierDefect.Base p
abbrev Hull := ArtinSchreierDefect.Hull p
abbrev Extension := ArtinSchreierDefect.ArtinSchreierExtension p
abbrev inverseT := ArtinSchreierDefect.inverseT p

instance baseRankOne : Valuation.RankOne (Valued.v : Valuation (Base p) ℤᵐ⁰) where
  hom' := (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0)).comp
    MonoidWithZeroHom.ValueGroup₀.embedding
  strictMono' := (WithZeroMulInt.toNNReal_strictMono (by norm_num : (1 : ℝ≥0) < 2)).comp
    MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
  exists_val_nontrivial := by
    refine ⟨inverseT p, ?_, ?_⟩ <;> rw [ArtinSchreierDefect.inverseT_value p]
    · exact WithZero.coe_ne_zero
    · exact ne_of_gt (WithZero.exp_lt_exp.mpr (by norm_num : (0 : ℤ) < 1))

instance baseNorm : NontriviallyNormedField (Base p) :=
  Valued.toNontriviallyNormedField (Base p) ℤᵐ⁰

/-- A spectral valuation over the complete Laurent-series base. -/
def spectralValuation (E : Type*) [Field E] [Algebra (Base p) E]
    [Algebra.IsAlgebraic (Base p) E] :
    Valuation E ℝ≥0 where
  toFun x := ⟨spectralNorm (Base p) E x, spectralNorm_nonneg x⟩
  map_zero' := by ext; exact spectralNorm_zero
  map_one' := by ext; exact spectralNorm_one
  map_mul' x y := by ext; exact spectralAlgNorm_mul x y
  map_add_le_max' x y := isNonarchimedean_spectralNorm x y

instance hullValuativeRel : ValuativeRel (Hull p) :=
  .ofValuation (spectralValuation p (Hull p))

instance baseHullValuativeExtension : ValuativeExtension (Base p) (Hull p) where
  vle_iff_vle a b := by
    change spectralNorm (Base p) (Hull p) (algebraMap _ _ a) ≤
      spectralNorm (Base p) (Hull p) (algebraMap _ _ b) ↔ Valued.v a ≤ Valued.v b
    rw [spectralNorm_extends, spectralNorm_extends]
    exact Valued.toNormedField.norm_le_iff

instance extensionAlgebraic : Algebra.IsAlgebraic (Base p) (Extension p) :=
  Algebra.IsAlgebraic.trans (Base p) (Hull p) (Extension p)

instance extensionValuativeRel : ValuativeRel (Extension p) :=
  .ofValuation (spectralValuation p (Extension p))

instance hullExtensionValuativeExtension : ValuativeExtension (Hull p) (Extension p) where
  vle_iff_vle a b := by
    change spectralNorm (Base p) (Extension p) (algebraMap _ _ a) ≤
      spectralNorm (Base p) (Extension p) (algebraMap _ _ b) ↔
        spectralNorm (Base p) (Hull p) a ≤ spectralNorm (Base p) (Hull p) b
    rw [← spectralNorm.eq_of_tower, ← spectralNorm.eq_of_tower]

instance baseExtensionValuativeExtension : ValuativeExtension (Base p) (Extension p) where
  vle_iff_vle a b := by
    change spectralNorm (Base p) (Extension p) (algebraMap _ _ a) ≤
      spectralNorm (Base p) (Extension p) (algebraMap _ _ b) ↔ Valued.v a ≤ Valued.v b
    rw [spectralNorm_extends, spectralNorm_extends]
    exact Valued.toNormedField.norm_le_iff

/-- A prime-degree valuative extension with surjective `p`-th powers and ramification
index dividing the degree has index one. -/
theorem ramificationIdx_eq_one_of_pow_surjective
    (p : ℕ) [Fact p.Prime]
    (K L : Type*) [Field K] [Field L] [ValuativeRel K] [ValuativeRel L]
    [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
    (hpow : Function.Surjective (fun x : L ↦ x ^ p))
    (hdegree : Module.finrank K L = p)
    (hindex : ramificationIdx K L ∣ Module.finrank K L) :
    ramificationIdx K L = 1 := by
  have hindexp : ramificationIdx K L ∣ p := hdegree ▸ hindex
  rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hindexp with he1 | hep
  · exact he1
  have he1 : ramificationIdx K L = 1 := by
    apply ramificationIdx_eq_one_iff.mpr
    intro γ
    obtain ⟨x, rfl⟩ := valuation_surjective (K := L) γ
    by_cases hx : x = 0
    · exact ⟨0, by simp [hx]⟩
    obtain ⟨y, hy⟩ := hpow x
    have hy0 : y ≠ 0 := by
      intro h
      subst y
      change (0 : L) ^ p = x at hy
      rw [zero_pow (Fact.out : p.Prime).ne_zero] at hy
      exact hx hy.symm
    have hvy : valuation L y ≠ 0 := (valuation L).ne_zero_iff.mpr hy0
    let H := (Units.map (mapValueGroupWithZero K L).toMonoidHom).range
    have hi : H.index = p := hep
    have hupow := H.pow_index_mem (Units.mk0 (valuation L y) hvy)
    rw [hi] at hupow
    obtain ⟨u, hu⟩ := hupow
    refine ⟨u.val, ?_⟩
    change (Units.map (mapValueGroupWithZero K L).toMonoidHom) u = _ at hu
    have hv := congrArg Units.val hu
    simpa [← map_pow, hy] using hv
  exact he1

instance extensionCharP : CharP (Extension p) p :=
  charP_of_injective_algebraMap (algebraMap (Base p) (Extension p)).injective p

instance extensionPerfect : PerfectField (Extension p) :=
  Algebra.IsAlgebraic.perfectField (Hull p)

instance instScalarTowerBaseHullExtension :
    IsScalarTower (Base p) (Hull p) (Extension p) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The Artin–Schreier extension is the splitting field of its standard polynomial. -/
instance extensionIsSplittingField :
    Polynomial.IsSplittingField (Hull p) (Extension p)
      (ArtinSchreierDefect.standardPolynomial p) where
  splits' := by
    have hmap :
        map (algebraMap (Hull p) (Extension p))
            (ArtinSchreierDefect.standardPolynomial p) =
          ArtinSchreier.polynomial p
            (algebraMap (Hull p) (Extension p)
              (algebraMap (Base p) (Hull p) (inverseT p))) := by
      simp only [ArtinSchreierDefect.standardPolynomial, ArtinSchreier.polynomial,
        Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    have hr :
        (map (algebraMap (Hull p) (Extension p))
          (ArtinSchreierDefect.standardPolynomial p)).IsRoot
            (AdjoinRoot.root (ArtinSchreierDefect.standardPolynomial p)) :=
      AdjoinRoot.isRoot_root _
    have hs := ArtinSchreier.splits_of_root p
      (algebraMap (Hull p) (Extension p)
        (algebraMap (Base p) (Hull p) (inverseT p)))
      (AdjoinRoot.root (ArtinSchreierDefect.standardPolynomial p)) (by
        rw [← hmap]
        exact hr)
    rw [hmap]
    exact hs
  adjoin_rootSet' := by
    apply top_unique
    rw [← AdjoinRoot.adjoinRoot_eq_top]
    apply Algebra.adjoin_mono
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    rw [mem_rootSet']
    exact ⟨map_ne_zero (ArtinSchreier.monic p _).ne_zero,
      AdjoinRoot.eval₂_root (ArtinSchreierDefect.standardPolynomial p)⟩

instance extensionIsGalois : IsGalois (Hull p) (Extension p) :=
  IsGalois.of_separable_splitting_field
    (p := ArtinSchreierDefect.standardPolynomial p) (ArtinSchreier.separable p _)

instance extensionCompatible : (spectralValuation p (Extension p)).Compatible :=
  Valuation.Compatible.ofValuation _

/-- The spectral extension has ramification index one for every prime `p`. -/
theorem concrete_ramificationIdx : ramificationIdx (Hull p) (Extension p) = 1 := by
  apply ramificationIdx_eq_one_iff.mpr
  intro γ
  obtain ⟨x, rfl⟩ := valuation_surjective (K := Extension p) γ
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  obtain ⟨y, hy⟩ := surjective_frobenius (Extension p) p x
  have hy' : y ^ p = x := by
    rw [← frobenius_def (R := Extension p) (p := p)]
    exact hy
  let v := spectralValuation p (Extension p)
  have hvσ (σ : Gal(Extension p / Hull p)) : v (σ y) = v y := by
    ext
    exact (spectralNorm_eq_of_equiv (σ.restrictScalars (Base p)) y).symm
  have hnorm := Algebra.norm_eq_prod_automorphisms (Hull p) y
  have hvnorm :
      v (algebraMap (Hull p) (Extension p) ((Algebra.norm (Hull p)) y)) = v y ^ p := by
    rw [hnorm, map_prod]
    calc
      ∏ σ : Gal(Extension p / Hull p), v (σ y) =
          ∏ _σ : Gal(Extension p / Hull p), v y := by
        apply Finset.prod_congr rfl
        intro σ _
        exact hvσ σ
      _ = v y ^ Fintype.card Gal(Extension p / Hull p) := by simp
      _ = v y ^ p := by
        congr 1
        rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
          ArtinSchreierDefect.extension_degree p]
  refine ⟨valuation (Hull p) ((Algebra.norm (Hull p)) y), ?_⟩
  rw [mapValueGroupWithZero_valuation]
  apply (Valuation.veq_iff_eq (v := valuation (Extension p))).mp
  apply (Valuation.veq_iff_eq (v := v)).mpr
  rw [hvnorm, ← map_pow, hy']

/-- Raising both sides to a positive power preserves and reflects the valuative relation. -/
theorem pow_vle_pow_iff (L : Type*) [Field L] [ValuativeRel L]
    (x y : L) (n : ℕ) (hn : n ≠ 0) : x ^ n ≤ᵥ y ^ n ↔ x ≤ᵥ y := by
  constructor
  · intro h
    by_contra hxy
    exact (not_vle.mpr (pow_vlt_pow (not_vle.mp hxy) hn)) h
  · intro h
    exact pow_vle_pow h n

/-- Two compatible valuative relations on a purely inseparable extension agree. -/
theorem purelyInseparable_unique
    (K L : Type*) [Field K] [Field L] [Algebra K L] [ValuativeRel K]
    (q : ℕ) [ExpChar K q] [IsPurelyInseparable K L]
    (v₁ v₂ : ValuativeRel L)
    (h₁ : letI := v₁; ValuativeExtension K L)
    (h₂ : letI := v₂; ValuativeExtension K L) : v₁ = v₂ := by
  have hp : q ≠ 0 := expChar_pos K q |>.ne'
  have comparison (v : ValuativeRel L) (hv : letI := v; ValuativeExtension K L)
      (x y : L) (n : ℕ) (a b : K)
      (ha : algebraMap K L a = x ^ q ^ n) (hb : algebraMap K L b = y ^ q ^ n) :
      v.vle x y ↔ a ≤ᵥ b := by
    let := v
    let := hv
    rw [← pow_vle_pow_iff L x y (q ^ n) (pow_ne_zero _ hp), ← ha, ← hb]
    exact ValuativeExtension.vle_iff_vle a b
  ext x y
  obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem K q x
  obtain ⟨m, b, hb⟩ := IsPurelyInseparable.pow_mem K q y
  have ha' : algebraMap K L (a ^ q ^ m) = x ^ q ^ (n + m) := by
    rw [map_pow, ha, ← pow_mul, ← pow_add]
  have hb' : algebraMap K L (b ^ q ^ n) = y ^ q ^ (n + m) := by
    rw [map_pow, hb, ← pow_mul, ← pow_add, Nat.add_comm m n]
  exact (comparison v₁ h₁ x y (n + m) _ _ ha' hb').trans
    (comparison v₂ h₂ x y (n + m) _ _ ha' hb').symm

instance hullCharP : CharP (Hull p) p :=
  charP_of_injective_algebraMap (algebraMap (Base p) (Hull p)).injective p

theorem hull_isPerfectClosure :
    IsPerfectClosure (algebraMap (Base p) (Hull p)) p := inferInstance

theorem hull_unique (other : ValuativeRel (Hull p))
    (h : letI := other; ValuativeExtension (Base p) (Hull p)) :
    other = hullValuativeRel p :=
  purelyInseparable_unique (Base p) (Hull p) p other (hullValuativeRel p) h
    (baseHullValuativeExtension p)

@[deprecated (since := "2026-11-16")]
alias ramificationIndex_eq_one_of_pow_surjective := ramificationIdx_eq_one_of_pow_surjective
@[deprecated (since := "2026-11-16")] alias concrete_ramificationIndex := concrete_ramificationIdx

end ArtinSchreierDefect.General

/-! ### Backwards-compatible quadratic API -/

namespace ArtinSchreierDefect.Quadratic

open ArtinSchreierBridge IsLocalRing
open scoped ValuativeRel BigOperators

abbrev Base := General.Base 2
abbrev Hull := General.Hull 2
abbrev Extension := General.Extension 2
abbrev inverseT := General.inverseT 2

instance baseRankOne : Valuation.RankOne (Valued.v : Valuation Base ℤᵐ⁰) :=
  General.baseRankOne 2

instance baseNorm : NontriviallyNormedField Base := General.baseNorm 2

/-- The original spectral valuation at `p = 2`. -/
abbrev spectralValuation (E : Type*) [Field E] [Algebra Base E]
    [Algebra.IsAlgebraic Base E] : Valuation E ℝ≥0 :=
  General.spectralValuation 2 E

instance hullValuativeRel : ValuativeRel Hull := General.hullValuativeRel 2

instance baseHullValuativeExtension : ValuativeExtension Base Hull :=
  General.baseHullValuativeExtension 2

instance extensionAlgebraic : Algebra.IsAlgebraic Base Extension :=
  General.extensionAlgebraic 2

instance extensionValuativeRel : ValuativeRel Extension :=
  General.extensionValuativeRel 2

instance hullExtensionValuativeExtension : ValuativeExtension Hull Extension :=
  General.hullExtensionValuativeExtension 2

instance baseExtensionValuativeExtension : ValuativeExtension Base Extension :=
  General.baseExtensionValuativeExtension 2

/-- The original quadratic ramification lemma. -/
theorem ramificationIdx_eq_one_of_square_surjective
    (K L : Type*) [Field K] [Field L] [ValuativeRel K] [ValuativeRel L]
    [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
    (hsquare : Function.Surjective (fun x : L ↦ x ^ 2))
    (hdegree : Module.finrank K L = 2) : ramificationIdx K L = 1 := by
  apply General.ramificationIdx_eq_one_of_pow_surjective 2 K L hsquare hdegree
  have hepos := one_le_ramificationIdx (K := K) (L := L)
  have hfpos := inertiaDeg_pos (K := K) (L := L)
  have hbound := ramificationIdx_mul_inertiaDeg_le_finrank (K := K) (L := L)
  rw [hdegree] at hbound
  have hele : ramificationIdx K L ≤ 2 := by nlinarith
  have he : ramificationIdx K L = 1 ∨ ramificationIdx K L = 2 := by omega
  rw [hdegree]
  rcases he with he | he <;> simp [he]

instance extensionCharP : CharP Extension 2 := General.extensionCharP 2

instance extensionPerfect : PerfectField Extension := General.extensionPerfect 2

/-- The original ramification-index computation at `p = 2`. -/
theorem concrete_ramificationIdx : ramificationIdx Hull Extension = 1 :=
  General.concrete_ramificationIdx 2

/-- Raising both sides to a positive power preserves and reflects the valuative relation. -/
theorem pow_vle_pow_iff (L : Type*) [Field L] [ValuativeRel L]
    (x y : L) (n : ℕ) (hn : n ≠ 0) : x ^ n ≤ᵥ y ^ n ↔ x ≤ᵥ y :=
  General.pow_vle_pow_iff L x y n hn

/-- Two compatible valuative relations on a purely inseparable extension agree. -/
theorem purelyInseparable_unique
    (K L : Type*) [Field K] [Field L] [Algebra K L] [ValuativeRel K]
    (q : ℕ) [ExpChar K q] [IsPurelyInseparable K L]
    (v₁ v₂ : ValuativeRel L)
    (h₁ : letI := v₁; ValuativeExtension K L)
    (h₂ : letI := v₂; ValuativeExtension K L) : v₁ = v₂ :=
  General.purelyInseparable_unique K L q v₁ v₂ h₁ h₂

instance hullCharP : CharP Hull 2 := General.hullCharP 2

theorem hull_isPerfectClosure : IsPerfectClosure (algebraMap Base Hull) 2 :=
  General.hull_isPerfectClosure 2

theorem hull_unique (other : ValuativeRel Hull)
    (h : letI := other; ValuativeExtension Base Hull) : other = hullValuativeRel :=
  General.hull_unique 2 other h

instance instScalarTowerBaseHullExtension : IsScalarTower Base Hull Extension :=
  General.instScalarTowerBaseHullExtension 2

@[deprecated (since := "2026-11-16")]
alias ramificationIndex_eq_one_of_square_surjective := ramificationIdx_eq_one_of_square_surjective
@[deprecated (since := "2026-11-16")] alias concrete_ramificationIndex := concrete_ramificationIdx

end ArtinSchreierDefect.Quadratic

namespace ArtinSchreierDefect.General

open ArtinSchreierBridge

variable (p : ℕ) [Fact p.Prime]

instance hullCompatible : (spectralValuation p (Hull p)).Compatible :=
  Valuation.Compatible.ofValuation (spectralValuation p (Hull p))

instance hullIsRankLeOne : IsRankLeOne (Hull p) :=
  IsRankLeOne.of_compatible_mulArchimedean (spectralValuation p (Hull p))

theorem exp_one_ne_one : WithZero.exp (1 : ℤ) ≠ (1 : ℤᵐ⁰) := by
  intro h
  have : WithZero.exp (0 : ℤ) < WithZero.exp (1 : ℤ) :=
    WithZero.exp_lt_exp.mpr (by norm_num : (0 : ℤ) < 1)
  simp [h] at this

instance baseIsNontrivial : IsNontrivial (Base p) := by
  have : Valuation.Compatible (Valued.v : Valuation (Base p) ℤᵐ⁰) :=
    Valuation.Compatible.ofValuation _
  refine ⟨valuation (Base p) (inverseT p), ?_, ?_⟩
  · intro h
    have : inverseT p = (0 : Base p) := (Valuation.zero_iff (valuation (Base p))).mp h
    exact (HahnSeries.single_ne_zero (by exact one_ne_zero)) this
  · intro h
    have hvle : Valued.v (inverseT p) = 1 := by
      have hle : inverseT p ≤ᵥ (1 : Base p) :=
        (Valuation.vle_iff_le (valuation (Base p))).mpr (le_of_eq h)
      have hge : (1 : Base p) ≤ᵥ inverseT p :=
        (Valuation.vle_iff_le (valuation (Base p)) (x := (1 : Base p))
          (y := inverseT p)).mpr
          (by simpa using (le_of_eq h.symm))
      apply le_antisymm
      · simpa [map_one] using
          (Valuation.vle_iff_le (Valued.v : Valuation (Base p) ℤᵐ⁰)).mp hle
      · simpa [map_one] using
          (Valuation.vle_iff_le (Valued.v : Valuation (Base p) ℤᵐ⁰)
            (x := (1 : Base p)) (y := inverseT p)).mp hge
    exact exp_one_ne_one ((ArtinSchreierDefect.inverseT_value p).symm.trans hvle)

theorem base_vle_iff_norm (x y : Base p) : x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ :=
  Valued.toNormedField.norm_le_iff (x := x) (x' := y) |>.symm

/-- Any valuative relation on the Artin–Schreier extension that is compatible with
the hull (equivalently, with the complete Laurent base) coincides with the
spectral relation. This uses completeness of `F_p((t))`, not henselianity of the
hull's valuation ring. -/
theorem unique_extension (other : ValuativeRel (Extension p))
    (h : letI := other; ValuativeExtension (Hull p) (Extension p)) :
    other = extensionValuativeRel p := by
  let := other
  let := h
  have hBase : ValuativeExtension (Base p) (Extension p) :=
    ValuativeExtension.comp (K := Base p) (F := Hull p) (L := Extension p)
  have : IsRankLeOne (Extension p) :=
    ValuativeRel.IsRankLeOne.of_finiteDimensional (Hull p) (Extension p)
  have : IsNontrivial (Extension p) :=
    ValuativeRel.IsNontrivial.of_valuativeExtension (Base p) (Extension p)
  have : Algebra.IsAlgebraic (Base p) (Extension p) := extensionAlgebraic p
  have hcmp := unique_valuativeRel_of_complete (K := Base p) (L := Extension p)
    (base_vle_iff_norm p) other hBase
  refine ValuativeRel.ext ?_
  funext x y
  exact propext ((hcmp x y).trans Iff.rfl)

end ArtinSchreierDefect.General

namespace ArtinSchreierDefect.General

open ArtinSchreierBridge IsLocalRing
open scoped ValuativeRel BigOperators

/-- Every compatible valuative relation on the Artin–Schreier extension equals the
spectral one. -/
theorem extension_eq_spectral (p : ℕ) [Fact p.Prime]
    (w : Extensions (Hull p) (Extension p)) :
    w.val = extensionValuativeRel p :=
  unique_extension p w.val w.property

instance baseCompatible (p : ℕ) [Fact p.Prime] :
    (Valued.v : Valuation (Base p) ℤᵐ⁰).Compatible :=
  Valuation.Compatible.ofValuation _

instance hullPerfect (p : ℕ) [Fact p.Prime] : PerfectField (Hull p) :=
  perfectClosure.perfectField (F := Base p) (E := AlgebraicClosure (Base p))

end ArtinSchreierDefect.General

namespace ArtinSchreierDefect.Quadratic

open ArtinSchreierBridge IsLocalRing
open scoped ValuativeRel BigOperators

instance hullCompatible : (spectralValuation Hull).Compatible := General.hullCompatible 2

instance hullIsRankLeOne : IsRankLeOne Hull := General.hullIsRankLeOne 2

theorem exp_one_ne_one : WithZero.exp (1 : ℤ) ≠ (1 : ℤᵐ⁰) :=
  General.exp_one_ne_one

instance baseIsNontrivial : IsNontrivial Base := General.baseIsNontrivial 2

theorem base_vle_iff_norm (x y : Base) : x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ :=
  General.base_vle_iff_norm 2 x y

/-- Any compatible valuative relation on the quadratic extension equals the spectral one. -/
theorem unique_extension (other : ValuativeRel Extension)
    (h : letI := other; ValuativeExtension Hull Extension) :
    other = extensionValuativeRel :=
  General.unique_extension 2 other h

/-- Every compatible valuative relation on the quadratic extension equals the spectral one. -/
theorem extension_eq_spectral (w : Extensions Hull Extension) :
    w.val = extensionValuativeRel :=
  General.extension_eq_spectral 2 w

instance baseCompatible : (Valued.v : Valuation Base ℤᵐ⁰).Compatible :=
  General.baseCompatible 2

instance extensionCompatible : (spectralValuation Extension).Compatible :=
  General.extensionCompatible 2

instance hullPerfect : PerfectField Hull := General.hullPerfect 2

end ArtinSchreierDefect.Quadratic
