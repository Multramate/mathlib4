/-
Copyright (c) 2025 David Kurniadi Angdinata, Sriram Chinthalagiri Venkata, and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata, Sriram Chinthalagiri Venkata, Junyan Xu
-/
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.Algebra
/-!
# Coordinate ring of an elliptic curve

We show that the (affine) coordinate ring of an elliptic curve is a Dedekind domain.

See https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Non-principal.20ideal.20in.20Dedekind.20domain/near/538662428
for a proof outline.
-/

open Ideal Polynomial

open scoped Bivariate nonZeroDivisors

attribute [local instance] algebra

noncomputable section CommRing

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

abbrev Ideal.Quotient.algebraQuotientOfMapLE {I : Ideal R} {J : Ideal A}
    (h : I.map (algebraMap R A) ≤ J) : Algebra (R ⧸ I) (A ⧸ J) :=
  Ideal.Quotient.algebraQuotientOfLEComap <| Ideal.le_comap_of_map_le h

abbrev Ideal.Quotient.isScalarTowerQuotient {I : Ideal R} {J : Ideal A}
    (h : I.map (algebraMap R A) ≤ J) :
    have : Algebra (R ⧸ I) (A ⧸ J) := algebraQuotientOfMapLE h
    IsScalarTower R (R ⧸ I) (A ⧸ J) :=
  let := algebraQuotientOfMapLE h
  IsScalarTower.of_algebraMap_eq <| congrFun rfl

abbrev Ideal.Quotient.isScalarTowerPolynomialQuotient {I : Ideal R[X]} {J : Ideal A[X]}
    (h : I.map (algebraMap R[X] A[X]) ≤ J) :
    have : Algebra (R[X] ⧸ I) (A[X] ⧸ J) := algebraQuotientOfMapLE h
    IsScalarTower R (R[X] ⧸ I) (A[X] ⧸ J) :=
  let := algebraQuotientOfMapLE h
  .of_algebraMap_eq' <| congrArg (algebraMap ..).comp <| IsScalarTower.algebraMap_eq R R[X] _

instance (I : Ideal R[X]) : Algebra (R[X] ⧸ I) (A[X] ⧸ I.map (mapRingHom <| algebraMap R A)) :=
  Ideal.Quotient.algebraQuotientOfMapLE le_rfl

instance (I : Ideal R[X]) :
    IsScalarTower R (R[X] ⧸ I) (A[X] ⧸ I.map (mapRingHom <| algebraMap R A)) :=
  Ideal.Quotient.isScalarTowerPolynomialQuotient le_rfl

instance (p : R[X]) : Algebra (AdjoinRoot p) (AdjoinRoot <| p.map <| algebraMap R A) :=
  Ideal.Quotient.algebraQuotientOfMapLE <| by simp [Ideal.map_span]

instance (p : R[X]) : IsScalarTower R (AdjoinRoot p) (AdjoinRoot <| p.map <| algebraMap R A) :=
  Ideal.Quotient.isScalarTowerPolynomialQuotient <| by simp [Ideal.map_span]

def AdjoinRoot.isFractionRing [IsDomain R] [IsFractionRing R A] {p : R[X]} (prime : Prime p)
    (degree : degree p ≠ 0) :
    IsFractionRing (AdjoinRoot p) (AdjoinRoot <| p.map <| algebraMap R A) := by
  have ne_zero : p ≠ 0 := fun h ↦ not_prime_zero <| h ▸ prime
  have isDomain : IsDomain <| AdjoinRoot p := isDomain_of_prime prime
  have isAlgebraic (x : AdjoinRoot p) : IsAlgebraic R x :=
    Algebra.isAlgebraic_adjoin_singleton_iff.mpr (isAlgebraic_root ne_zero) x <|
      by simpa only [adjoinRoot_eq_top] using Algebra.mem_top
  have isLocalization := isLocalization R⁰ A
  rw [IsFractionRing, ← IsLocalization.iff_of_le_of_exists_dvd]
  · exact IsLocalization.of_surjective (R⁰.map C) A[X] _ Quotient.mk_surjective _
      Quotient.mk_surjective rfl <| fun _ h ↦ by
        rcases mem_span_singleton'.mp <| Quotient.eq_zero_iff_mem.mp h with ⟨_, rfl⟩
        exact mul_mem_left _ _ <| mem_map_of_mem _ <| Quotient.mk_singleton_self ..
  · rintro _ ⟨_, ⟨_, h, rfl⟩, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero <| mem_nonZeroDivisors_iff_ne_zero.mp h
      ∘ (injective_iff_map_eq_zero _).mp (of.injective_of_degree_ne_zero degree) _
  · intro _ h
    rcases (isAlgebraic _).exists_nonzero_dvd h with ⟨_, h, _, h'⟩
    exact ⟨_, ⟨_, ⟨_, mem_nonZeroDivisors_of_ne_zero h, rfl⟩, rfl⟩, _, h'⟩

end CommRing

noncomputable section

abbrev Polynomial.toRatFunc {R} [CommRing R] : R[X] →+* FractionRing R[X] :=
  algebraMap ..

lemma Polynomial.toRatFunc_X_ne_zero {R} [CommRing R] [Nontrivial R] : (X : R[X]).toRatFunc ≠ 0 :=
  by simp

namespace WeierstrassCurve

def Affine.CoordinateRing.variableChange {R} [CommRing R] (W : WeierstrassCurve.Affine R)
    (e : VariableChange R) : W.CoordinateRing ≃ₐ[R] (e • W).CoordinateRing := by
  sorry /- The isomorphism is given by `(X, Y) ↔ (u²X + r, u³Y + u²sX + t)`. -/

namespace Affine
/- A type synonym of WeierstrassCurve to give access to affine versions of the Weierstrass
polynomial and coordinate ring, etc. -/

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (E : Affine R)

notation:10000 R"(X)" => FractionRing R[X]

/-- Another implementation of the function field of a Weierstrass curve, as `R(X)[Y]` modulo
the Weierstrass polynomial. -/
abbrev FunctionField' := AdjoinRoot <| E.polynomial.map <| algebraMap R[X] R(X)
-- another implementation could be R(X) ⊗[R[X]] E.CoordinateRing

def irreducible_polynomial' : Irreducible <| E.polynomial.map <| algebraMap R[X] R(X) :=
  monic_polynomial.irreducible_iff_irreducible_map_fraction_map.mp irreducible_polynomial

def prime_polynomial' : Prime <| E.polynomial.map <| algebraMap R[X] R(X) :=
  E.irreducible_polynomial'.prime

instance : Fact <| Irreducible <| E.polynomial.map <| algebraMap R[X] R(X) :=
  ⟨E.irreducible_polynomial'⟩

example : Algebra E.CoordinateRing E.FunctionField' := inferInstance
example : IsScalarTower R[X] E.CoordinateRing E.FunctionField' := inferInstance
instance : Module.Free R[X] E.CoordinateRing := .of_basis <| CoordinateRing.basis E
instance : Module.Finite R[X] E.CoordinateRing := monic_polynomial.finite_adjoinRoot
instance : FiniteDimensional R(X) E.FunctionField' := (monic_polynomial.map _).finite_adjoinRoot

instance : IsFractionRing E.CoordinateRing E.FunctionField' :=
  AdjoinRoot.isFractionRing irreducible_polynomial.prime <| E.degree_polynomial ▸ two_ne_zero

example : FaithfulSMul E.CoordinateRing E.FunctionField' := inferInstance

theorem isIntegral_coordinateRing_iff {f : E.FunctionField'} :
    IsIntegral E.CoordinateRing f ↔ IsIntegral R[X] f :=
  ⟨isIntegral_trans f, IsIntegral.tower_top⟩

-- this deals with the q = 0 case
theorem isIntegral_algebraMap_iff {p : R(X)} :
    IsIntegral R[X] (algebraMap _ E.FunctionField' p) ↔ p ∈ toRatFunc.range := by
  sorry

variable (p q : R(X))

-- rename to `addMulY`?
def comb : E.FunctionField' := p • 1 + q • .mk _ X

def trace : R(X) :=
  2 * p - q * (C E.a₁ * X + C E.a₃).toRatFunc

def norm : R(X) :=
  p ^ 2 - p * q * (C E.a₁ * X + C E.a₃).toRatFunc -
    q ^ 2 * (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆).toRatFunc

-- An arbitrary element of the function field can be written in the form p(X) + q(X)Y
theorem FunctionField'.exists_comb_eq (f : E.FunctionField') : ∃ p q : R(X), E.comb p q = f := by
  sorry
  -- mimic the proof of `CoordinateRing.exists_smul_basis_eq`
  -- may need to develop some basis API

-- If q ≠ 0, the minimal polynomial of f = p + qY is quadratic, given by Z² - Tr(f)Z + N(f).
theorem minpoly_comb (hq : q ≠ 0) :
    minpoly R(X) (E.comb p q) = X ^ 2 - C (E.trace p q) * X + C (E.norm p q) := by
  refine (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_).symm
  · sorry
  · sorry
  · monicity!

omit [IsDomain R] [UniqueFactorizationMonoid R] in
theorem trace_sq_sub_four_mul_norm :
    E.trace p q ^ 2 - 4 * E.norm p q = q ^ 2 * E.twoTorsionPolynomial.toPoly.toRatFunc := by
    unfold trace norm twoTorsionPolynomial Cubic.toPoly b₂ b₄ b₆
    simp only [Polynomial.toRatFunc, map_add, map_mul, map_pow, map_ofNat]
    ring

theorem isIntegral_of_sq_sub_mem_range {R A} [CommRing R] [Ring A] [Algebra R A] {r₀ r₁ : R} {a : A}
    (h : a ^ 2 - algebraMap R A r₁ * a - algebraMap R A r₀ ∈ (algebraMap R A).range) :
    IsIntegral R a := by
  have ⟨r, hr⟩ := h
  rw [eq_comm, ← sub_eq_zero] at hr
  exact ⟨X ^ 2 - C r₁ * X - C (r₀ + r), by monicity <;> decide, by simpa [← sub_sub]⟩

/- If q and N(p+qY) lie in R[X], then p satisfies a monic quadratic equation
with coefficients in R[X], so p is integral over R[X] and therefore in R[X]. -/
theorem left_mem_of_right_mem_of_norm_mem (hq : q ∈ toRatFunc.range)
    (hn : E.norm p q ∈ toRatFunc.range) : p ∈ toRatFunc.range := by
  sorry -- obtain from hq, rewrite E.norm, then apply `isIntegral_of_sq_add_mem_range`

theorem trace_mem_of_isIntegral {p q : R(X)} (int : IsIntegral R[X] <| E.comb p q) :
    E.trace p q ∈ toRatFunc.range := by
  sorry -- use minpoly.isIntegrallyClosed_eq_field_fractions'

theorem norm_mem_of_isIntegral {p q : R(X)} (int : IsIntegral R[X] <| E.comb p q) :
    E.norm p q ∈ toRatFunc.range := by
  sorry -- ditto

variable {K : Type*} [Field K] (E : Affine K) {p q : K(X)} (int : IsIntegral K[X] <| E.comb p q)

theorem left_mem_of_right_mem (int : IsIntegral K[X] <| E.comb p q) (hq : q ∈ toRatFunc.range) :
    p ∈ toRatFunc.range := by
  have ⟨f, hf⟩ := hq
  have := E.norm_mem_of_isIntegral int
  rw [← hf, norm, mul_assoc, mul_comm, ← map_pow, ← map_mul, ← map_mul] at this
  exact (isIntegrallyClosed_iff K(X)).mp inferInstance (isIntegral_of_sq_sub_mem_range this)

variable [E.IsElliptic]

section IsUnit2

variable (h2 : IsUnit (2 : K))

include h2

theorem separable_twoTorsionPolynomial : E.twoTorsionPolynomial.toPoly.Separable := by
  have : NeZero (2 : K) := ⟨h2.ne_zero⟩
  have : NeZero (4 : K) := by
    rw [show (4 : K) = 2 * 2 by norm_num1]
    exact NeZero.mul
  have h : E.twoTorsionPolynomial.discr ≠ 0 := twoTorsionPolynomial_discr_ne_zero _ h2 E.isUnit_Δ
  let F := SplittingField E.twoTorsionPolynomial.toPoly
  apply (nodup_aroots_iff_of_splits (K := F) _ _).mp
  · rw [aroots, ← Cubic.map_toPoly]
    exact (Cubic.discr_ne_zero_iff_roots_nodup four_ne_zero <| IsSplittingField.splits _ _).mp h
  · exact Cubic.ne_zero_of_a_ne_zero four_ne_zero
  exact IsSplittingField.splits _ _

include int in
/- Maybe extract a lemma for `UniqueFactorizationMonoid`. -/
theorem right_mem_of_isIntegral : q ∈ toRatFunc.range := by
  rcases IsFractionRing.exists_reduced_fraction (A := K[X]) (x := q) with ⟨f, g, h, h'⟩
  have ⟨l, hi⟩ : ∃ h : K[X], f * f * E.twoTorsionPolynomial.toPoly = h * (g * g) := by
    have := trace_sq_sub_four_mul_norm E p q
    rcases trace_mem_of_isIntegral E int, norm_mem_of_isIntegral E int with ⟨⟨tr, htr⟩, ⟨nm, hnm⟩⟩
    use tr ^ 2 - 4 * nm
    apply_fun toRatFunc using IsFractionRing.injective ..
    simp only [map_mul, map_sub, map_pow]
    rw [htr, hnm, map_ofNat, this, ← h', ← IsLocalization.mk'_spec' K(X) f g]
    ring1
  have hu : (g : K[X]) * g ∣ E.twoTorsionPolynomial.toPoly := by
    apply IsCoprime.dvd_of_dvd_mul_left (y := f * f) <| by
      apply IsCoprime.mul_right <;> exact h.isCoprime.symm.mul_left h.isCoprime.symm
    use l; linear_combination hi
  have he : IsUnit (g : K[X]) := (E.separable_twoTorsionPolynomial h2).squarefree _ hu
  use f * he.unit⁻¹
  simp [← h', div_eq_mul_inv]

end IsUnit2

section Char2

variable [CharP K 2]

theorem a₁_or_a₃_ne_zero_of_char_two : E.a₁ ≠ 0 ∨ E.a₃ ≠ 0 := by
  have h : Δ E ≠ 0 := isUnit_iff_ne_zero.mp <| (isElliptic_iff _).mp <| by assumption
  contrapose! h
  rw [Δ_of_char_two, h.left, h.right]
  ring1

omit [WeierstrassCurve.IsElliptic E] in
theorem trace_eq_of_char_two : E.trace p q = q * (C E.a₁ * X + C E.a₃).toRatFunc := by
  simp [trace, CharTwo.two_eq_zero, CharTwo.neg_eq]

include int

/- If a₁ = 0, then a₃ ≠ 0 by `a₁_or_a₃_ne_zero_of_char_two`, and Tr(p+qY) = a₃q ∈ K[X],
so q ∈ K[X]. -/
theorem right_mem_of_isIntegral_of_a₁_ne_zero (h : E.a₁ = 0) : q ∈ toRatFunc.range := by
  sorry

/- If a₁ ≠ 0, we may assume it is in normal form, so that a₁ = 1 and a₃ = a₄ = 0, and
a₆ = Δ ≠ 0 by `Δ_of_isCharTwoJNeZeroNF_of_char_two`.
We can come back to prove this assuming only a₁ ≠ 0 after we've shown the coordinate ring is
integrally closed. -/
theorem right_mem_of_isIntegral_of_isCharTwoJNeZeroNF [E.IsCharTwoJNeZeroNF] :
    q ∈ toRatFunc.range := by
  have hq : q * X.toRatFunc ∈ toRatFunc.range := by
    sorry -- we have Tr(p+qY) = qX in this case, so just use `trace_eq_of_char_two`
  have : IsIntegral K[X] (p * X.toRatFunc) := by
    sorry -- Since `E.norm p q ∈ K[X]`, we have `X² * E.norm p q ∈ K[X]` as well.
    -- Expand the definition of norm, and apply `isIntegral_of_sq_add_mem_range`
  have ⟨pX, hp⟩ : p * X.toRatFunc ∈ toRatFunc.range := by
    sorry -- since K[X] is integrally closed
  have ⟨qX, hq⟩ := hq
  have ⟨N, hN⟩ := E.norm_mem_of_isIntegral int
  have hN : pX ^ 2 + pX * qX * X + qX ^ 2 * (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₆) = X ^ 2 * N := by
    sorry -- X² times the definition of norm
  have hsq : pX.coeff 0 ^ 2 + qX.coeff 0 ^ 2 * E.a₆ = 0 := by
    have := congr_arg (·.coeff 0) hN -- compare the constant term of the two sides of hN
    sorry
  have hpx : pX.coeff 0 * qX.coeff 0 = 0 := by
    have := congr_arg (·.coeff 1) hN -- compare the X coefficient of the two sides of hN
    sorry -- We are in characteristic 2, so f² has no linear term for any polynomial f.
  have hp0 : pX.coeff 0 = 0 := by
    rcases mul_eq_zero.mp hpx with h1 | h2
    · exact h1
    · rw [h2, zero_pow two_ne_zero, zero_mul, add_zero, sq_eq_zero_iff] at hsq
      exact hsq
  have hq0 : qX.coeff 0 = 0 := by
    rw [hp0, zero_pow two_ne_zero, zero_add] at hsq
    rcases mul_eq_zero.mp hsq with h1 | h2
    · rw [sq_eq_zero_iff] at h1
      exact h1
    · exact absurd h2 (by rw [← Δ_of_isCharTwoJNeZeroNF_of_char_two]; exact E.isUnit_Δ.ne_zero)
  refine ⟨qX.divX, mul_right_cancel₀ toRatFunc_X_ne_zero ?_⟩
  conv_rhs => rw [← hq, ← qX.divX_mul_X_add, hq0, C_0, add_zero, map_mul]

end Char2

variable (h : IsUnit (2 : K) ∨ E.a₁ = 0 ∨ E.IsCharTwoJNeZeroNF)
include h

include int in
theorem comb_mem_of_isIntegral : E.comb p q ∈ (algebraMap E.CoordinateRing _).range := by
  have hq : q ∈ toRatFunc.range := by
    by_cases h2 : IsUnit (2 : K)
    · exact E.right_mem_of_isIntegral int h2
    have h₂ := h2
    rw [isUnit_iff_ne_zero, Ne, not_not] at h2
    have := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero Nat.prime_two h2)
    obtain h | h := h.resolve_left h₂
    · exact E.right_mem_of_isIntegral_of_a₁_ne_zero int h
    · exact E.right_mem_of_isIntegral_of_isCharTwoJNeZeroNF int
  obtain ⟨p, rfl⟩ := E.left_mem_of_right_mem int hq
  obtain ⟨q, rfl⟩ := hq
  refine ⟨p • 1 + q • .mk _ X, ?_⟩
  simp only [Algebra.smul_def, mul_one, map_add, map_mul, comb]
  congr!
  · exact congr_arg (⟦·⟧) (map_C ..)
  · exact congr_arg (⟦·⟧) (map_C ..)
  · exact congr_arg (⟦·⟧) (map_X _)

namespace CoordinateRing

/-- The affine coordinate ring of an elliptic curve is the integral closure of the
1-variable polynomial ring in the function field. -/
private theorem isIntegralClosure :
    IsIntegralClosure E.CoordinateRing K[X] E.FunctionField' := by
  refine ⟨IsFractionRing.injective .., fun {f} ↦ ⟨fun int ↦ ?_, ?_⟩⟩
  · obtain ⟨p, q, rfl⟩ := f.exists_comb_eq; exact E.comb_mem_of_isIntegral int h
  · rintro ⟨f, rfl⟩; exact isIntegral_trans _ (isIntegral_algebraMap ..)

private theorem isIntegrallyClosedIn : IsIntegrallyClosedIn E.CoordinateRing E.FunctionField' :=
  have := CoordinateRing.isIntegralClosure E h
  .of_isIntegralClosure K[X]

end CoordinateRing

omit h

instance : IsIntegrallyClosed E.CoordinateRing := by
  by_cases h2 : (2 : K) = 0
  · have := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero Nat.prime_two h2)
    by_cases h₁ : E.a₁ = 0
    · exact (isIntegrallyClosed_iff_isIntegrallyClosedIn _).mpr
        (CoordinateRing.isIntegrallyClosedIn E <| .inr <| .inl h₁)
    · have := E.toCharTwoJNeZeroNF h₁
      have := (isIntegrallyClosed_iff_isIntegrallyClosedIn _).mpr
        (CoordinateRing.isIntegrallyClosedIn _ <| .inr <| .inr <| E.toCharTwoJNeZeroNF_spec h₁)
      exact .of_equiv (CoordinateRing.variableChange E (E.toCharTwoJNeZeroNF h₁)).toRingEquiv.symm
  · exact (isIntegrallyClosed_iff_isIntegrallyClosedIn _).mpr
      (CoordinateRing.isIntegrallyClosedIn E <| .inl <| Ne.isUnit h2)

example : IsIntegralClosure E.CoordinateRing K[X] E.FunctionField' := inferInstance
example : IsIntegrallyClosedIn E.CoordinateRing E.FunctionField' := inferInstance

theorem coeff_ne_zero_is_separable {R} [Field R] {f : R[X]} (p n : ℕ) [HF : CharP R p]
    (irred : Irreducible f) (not_dvd : ¬p∣n) (coeff_ne_zero : f.coeff n ≠ 0) : f.Separable := by
  rcases Polynomial.separable_or p irred with h|h
  · assumption
  apply And.symm at h
  rw [← Classical.not_imp] at h
  contrapose! h
  intro j
  contrapose! j
  intro x irrx
  by_cases hpn : 0 < p
  · have k : ((expand R p) x).coeff n = 0 := by
      convert Polynomial.coeff_expand hpn x n
      rw [if_neg not_dvd]
    intro i
    rw [Polynomial.ext_iff] at i
    have jp : ((expand R p) x).coeff n = f.coeff n := by exact i n
    rw [k] at jp
    apply coeff_ne_zero
    symm
    assumption
  · simp only [not_lt, nonpos_iff_eq_zero] at hpn
    contrapose! h
    have : CharZero R := by
      rw [← CharP.charP_zero_iff_charZero]
      rw [hpn] at HF
      assumption
    apply Irreducible.separable irred

instance : Algebra.IsSeparable K(X) E.FunctionField' := by
  rw [Algebra.isSeparable_iff]
  intro x
  rcases FunctionField'.exists_comb_eq E x with ⟨p',q',rfl⟩
  constructor
  · apply IsIntegral.add
    · apply IsIntegral.smul
      exact isIntegral_one
    apply IsIntegral.smul
    apply AdjoinRoot.isIntegral_root' _
    apply Polynomial.Monic.map
    exact monic_polynomial
  · apply Field.isSeparable_add
    · have : (1 : E.FunctionField') =
        (AdjoinRoot.of (Polynomial.map (algebraMap K[X] K(X)) E.polynomial)) (1:K(X)) := rfl
      rw [this]
      have jr : p' • (AdjoinRoot.of (Polynomial.map (algebraMap K[X] K(X)) E.polynomial)) 1 =
                (AdjoinRoot.of (Polynomial.map (algebraMap K[X] K(X)) E.polynomial)) p' := by
        rw [AdjoinRoot.smul_of, smul_eq_mul]
        simp
      rw [jr]
      apply isSeparable_algebraMap p'
    have hr: q' • (AdjoinRoot.mk (Polynomial.map (algebraMap K[X] K(X)) E.polynomial) X) =
             (AdjoinRoot.of (Polynomial.map (algebraMap K[X] K(X)) E.polynomial)) q' •
             (AdjoinRoot.mk (Polynomial.map (algebraMap K[X] K(X)) E.polynomial) X) := by
      rw [AdjoinRoot.smul_mk, smul_eq_C_mul]
      rfl
    rw [hr,smul_eq_mul]
    apply Field.isSeparable_mul
    · apply isSeparable_algebraMap q'
    have ir : minpoly K(X) (AdjoinRoot.root (Polynomial.map (algebraMap K[X] K(X)) E.polynomial)) =
        (Polynomial.map (algebraMap K[X] K(X)) E.polynomial) := by
      rw [AdjoinRoot.minpoly_root]
      · have pr : (Polynomial.map (algebraMap K[X] K(X)) E.polynomial).leadingCoeff = 1 := by
          apply Polynomial.Monic.leadingCoeff
          apply Polynomial.Monic.map
          exact monic_polynomial
        rw [pr]
        simp
      apply Polynomial.map_monic_ne_zero
      exact monic_polynomial
    rw [AdjoinRoot.mk_X, IsSeparable]
    obtain _ | ⟨p, ju, iu⟩ := CharP.exists' K(X)
    · apply Irreducible.separable
      rw [ir]
      apply (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map _).mp
      · exact irreducible_polynomial
      · exact monic_polynomial
    by_cases h2 : p = 2
    · apply coeff_ne_zero_is_separable
      · rw [ir]
        apply (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map _).mp
        · exact irreducible_polynomial
        · exact monic_polynomial
      · have lo : ¬ p ∣ 1:= by
          rw [h2]
          exact Nat.two_dvd_ne_zero.mpr rfl
        exact lo
      rw [ir]
      simp only [coeff_map, ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
      rw [polynomial_eq]
      intro zi
      simp only [Cubic.coeff_eq_c] at zi
      have yu : E.a₁ = 0 ∧ E.a₃ = 0 := by
        contrapose! zi
        by_cases yu : E.a₁ ≠ 0
        · apply Cubic.ne_zero_of_c_ne_zero
          simpa
        · apply Cubic.ne_zero_of_d_ne_zero
          simp only [ne_eq]
          apply zi
          push_neg at yu
          assumption
      contrapose! yu
      have gu : CharP K 2 := by
        apply (Algebra.charP_iff _ K(X) _).mpr
        rw [h2] at iu
        assumption
      convert a₁_or_a₃_ne_zero_of_char_two E
      exact imp_iff_not_or
    · apply coeff_ne_zero_is_separable
      · rw [ir]
        apply (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map _).mp
        · exact irreducible_polynomial
        · exact monic_polynomial
      · have lo : ¬ p ∣ 2 := by
          contrapose! h2
          symm
          apply (Nat.Prime.dvd_iff_eq _ _).mp
          · assumption
          · exact Nat.prime_two
          apply Nat.Prime.ne_one
          rw [fact_iff] at ju
          assumption
        exact lo
      rw [ir]
      simp only [coeff_map, ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
      rw [polynomial_eq]
      intro zi
      simp at zi

instance : IsDedekindDomain E.CoordinateRing :=
  IsIntegralClosure.isDedekindDomain K[X] K(X) E.FunctionField' E.CoordinateRing

end WeierstrassCurve.Affine
