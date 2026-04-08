/-
Copyright (c) 2025 David Kurniadi Angdinata, Sriram Chinthalagiri Venkata, and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata, Sriram Chinthalagiri Venkata, Junyan Xu
-/
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Polynomial.SpecificDegree
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

lemma Polynomial.coeff_sq_of_odd {R : Type*} [CommSemiring R] [CharP R 2]
    (f : R[X]) {n : ℕ} (hn : ¬ 2 ∣ n) : (f ^ 2).coeff n = 0 := by
  rw [← map_frobenius_expand, coeff_map, coeff_expand two_pos, if_neg hn, map_zero]

namespace WeierstrassCurve

section VariableChangeAPI

variable {R : Type*} [CommRing R] (W : WeierstrassCurve.Affine R) (e : VariableChange R)

open scoped Bivariate

-- The forward substitution applied to the Weierstrass polynomial gives u⁶ times the transformed
-- Weierstrass polynomial. The proof expands both sides, eliminates u⁻¹ using u * u⁻¹ = 1 at the
-- R level, then closes with ring.
lemma Affine.variableChange_polynomial : let u : R := e.u;
    W.polynomial.eval₂
      ((C : R[X] →+* R[X][Y]).comp (Polynomial.aeval (C u ^ 2 * X + C e.r)).toRingHom)
      (C (C (u ^ 3)) * Y + C (C (u ^ 2 * e.s) * X + C e.t)) =
    C (C (u ^ 6)) * (e • W).polynomial := by
  intro u
  set ui : R := ↑e.u⁻¹
  -- Expand polynomial and variableChange definitions, then eval₂
  simp only [Affine.polynomial, variableChange_def]
  simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X,
    RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    map_add, map_sub, map_mul, map_pow, map_ofNat,
    Polynomial.aeval_C, Polynomial.aeval_X]
  simp only [← C_eq_algebraMap]
  -- Normalize both sides to sums of monomials in C(C u), C(C ui), C(C ...), C X, Y
  ring_nf
  -- Fold ↑e.u⁻¹ back to ui (ring_nf unfolds set definitions)
  conv_rhs => simp only [show (↑e.u⁻¹ : R) = ui from rfl]
  -- Establish C(C u) * C(C ui) = 1 and collapse C(C u)^6 * C(C ui)^k → C(C u)^(6-k)
  have hCCu : (C (C u) : R[X][Y]) * C (C ui) = 1 := by
    rw [← C_mul, ← C_mul, e.u.mul_inv, map_one, map_one]
  -- Eliminate all C(C ui)^k terms via linear_combination with pow_mul_pow_eq_one
  linear_combination
    -(Y * C (C e.s) * C X * 2 + Y * C X * C (C W.a₁)) *
      C (C u) ^ 5 * hCCu -
    (C (C e.s) * C X ^ 2 * C (C W.a₁) + C (C e.s) ^ 2 * C X ^ 2 -
      C X ^ 2 * C (C e.r) * 3 - C X ^ 2 * C (C W.a₂)) *
      C (C u) ^ 4 * pow_mul_pow_eq_one 2 hCCu -
    (Y * C (C e.t) * 2 + Y * C (C W.a₁) * C (C e.r) + Y * C (C W.a₃)) *
      C (C u) ^ 3 * pow_mul_pow_eq_one 3 hCCu -
    (C (C e.s) * C X * C (C e.t) * 2 + C (C e.s) * C X * C (C W.a₁) * C (C e.r) +
      C (C e.s) * C X * C (C W.a₃) + C X * C (C e.t) * C (C W.a₁) -
      C X * C (C e.r) * C (C W.a₂) * 2 - C X * C (C e.r) ^ 2 * 3 - C X * C (C W.a₄)) *
      C (C u) ^ 2 * pow_mul_pow_eq_one 4 hCCu -
    (C (C e.t) * C (C W.a₁) * C (C e.r) + C (C e.t) * C (C W.a₃) + C (C e.t) ^ 2 -
      C (C e.r) * C (C W.a₄) - C (C e.r) ^ 2 * C (C W.a₂) - C (C e.r) ^ 3 - C (C W.a₆)) *
      pow_mul_pow_eq_one 6 hCCu

/-- The inverse substitution applied to the transformed Weierstrass polynomial gives
`u⁻⁶` times the original polynomial. -/
lemma Affine.variableChange_polynomial_inv : let ui : R := ↑e.u⁻¹;
    (e • W).polynomial.eval₂
      ((C : R[X] →+* R[X][Y]).comp
        (Polynomial.aeval (C (ui ^ 2) * X + C (-e.r * ui ^ 2))).toRingHom)
      (C (C (ui ^ 3)) * Y +
        C (C (-e.s * ui ^ 3) * X + C ((e.r * e.s - e.t) * ui ^ 3))) =
    C (C (ui ^ 6)) * W.polynomial := by
  intro ui
  set u : R := ↑e.u
  simp only [Affine.polynomial]
  simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X,
    RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    map_add, map_sub, map_mul, map_pow, map_neg,
    Polynomial.aeval_C, Polynomial.aeval_X]
  simp only [← C_eq_algebraMap]
  simp only [variableChange_def]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  conv => simp only [show (↑e.u⁻¹ : R) = ui from rfl]
  ring_nf

/-- Composing the forward and inverse X-substitutions gives the identity. -/
lemma Affine.variableChange_aeval_comp : let u : R := e.u; let ui : R := ↑e.u⁻¹;
    Polynomial.aeval (C u ^ 2 * X + C e.r)
      (C (ui ^ 2) * X + C (-e.r * ui ^ 2)) = (X : R[X]) := by
  intro u ui
  simp only [map_add, map_mul, map_neg, Polynomial.aeval_C, Polynomial.aeval_X]
  simp only [← C_eq_algebraMap]
  have hui2 : C (ui ^ 2) * C u ^ 2 = (1 : R[X]) := by
    simp only [← C_pow, ← C_mul, ← C_1]; exact congr_arg C (pow_mul_pow_eq_one 2 e.u.inv_mul)
  linear_combination hui2 * X

/-- Composing the inverse and forward X-substitutions gives the identity. -/
lemma Affine.variableChange_aeval_comp_inv : let u : R := e.u; let ui : R := ↑e.u⁻¹;
    Polynomial.aeval (C (ui ^ 2) * X + C (-e.r * ui ^ 2))
      (C u ^ 2 * X + C e.r) = (X : R[X]) := by
  intro u ui
  simp only [map_add, map_mul, map_neg, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
  simp only [← C_eq_algebraMap, ← C_pow]
  have hu2 : C (u ^ 2) * C (ui ^ 2) = (1 : R[X]) := by
    rw [← C_mul, ← C_1]; exact congr_arg C (pow_mul_pow_eq_one 2 e.u.mul_inv)
  linear_combination hu2 * X - hu2 * C e.r

end VariableChangeAPI

private lemma mul_root_add_cancel {T : Type*} [CommRing T] {p : T[X]}
    {a b c d : AdjoinRoot p} (hab : a * b = 1) (hcd : a * c + d = 0) :
    a * (b * AdjoinRoot.root p + c) + d = AdjoinRoot.root p := by
  linear_combination hab * AdjoinRoot.root p + hcd

def Affine.CoordinateRing.variableChange {R} [CommRing R] (W : WeierstrassCurve.Affine R)
    (e : VariableChange R) : W.CoordinateRing ≃ₐ[R] (e • W).CoordinateRing := by
  /- The isomorphism sends (X, Y) ↔ (u²X + r, u³Y + u²sX + t).
     Built via AdjoinRoot.liftAlgHom in both directions, combined with AlgEquiv.ofAlgHom. -/
  let u : R := e.u
  let ui : R := ↑e.u⁻¹
  -- Forward map: X ↦ u²X' + r, Y ↦ u³Y' + u²sX' + t
  let ι : R[X] →ₐ[R] (e • W).CoordinateRing :=
    (IsScalarTower.toAlgHom R R[X] _).comp (Polynomial.aeval (C u ^ 2 * X + C e.r))
  let η : (e • W).CoordinateRing :=
    algebraMap R[X] _ (C (u ^ 3)) * AdjoinRoot.root _ +
    algebraMap R[X] _ (C (u ^ 2 * e.s) * X + C e.t)
  have hf : W.polynomial.eval₂ ι η = 0 := by
    rw [show (↑ι : R[X] →+* _) = (AdjoinRoot.mk (e • W).polynomial).comp
        ((C : R[X] →+* R[X][Y]).comp (Polynomial.aeval (C u ^ 2 * X + C e.r)).toRingHom) from rfl,
      show η = (AdjoinRoot.mk (e • W).polynomial)
        (C (C (u ^ 3)) * Y + C (C (u ^ 2 * e.s) * X + C e.t)) from by
        simp only [η, map_add, map_mul, ← AdjoinRoot.mk_X]; rfl,
      ← Polynomial.hom_eval₂, Affine.variableChange_polynomial,
      map_mul, AdjoinRoot.mk_self, mul_zero]
  -- Backward map: X' ↦ u⁻²X - ru⁻², Y' ↦ u⁻³Y + (-su⁻³)X + (rs-t)u⁻³
  let ι' : R[X] →ₐ[R] W.CoordinateRing :=
    (IsScalarTower.toAlgHom R R[X] _).comp (Polynomial.aeval (C (ui ^ 2) * X + C (-e.r * ui ^ 2)))
  let η' : W.CoordinateRing :=
    algebraMap R[X] _ (C (ui ^ 3)) * AdjoinRoot.root _ +
    algebraMap R[X] _ (C (-e.s * ui ^ 3) * X + C ((e.r * e.s - e.t) * ui ^ 3))
  have hb : (e • W).polynomial.eval₂ ι' η' = 0 := by
    rw [show (↑ι' : R[X] →+* _) = (AdjoinRoot.mk W.polynomial).comp
        ((C : R[X] →+* R[X][Y]).comp
          (Polynomial.aeval (C (ui ^ 2) * X + C (-e.r * ui ^ 2))).toRingHom) from rfl,
      show η' = (AdjoinRoot.mk W.polynomial)
        (C (C (ui ^ 3)) * Y +
          C (C (-e.s * ui ^ 3) * X + C ((e.r * e.s - e.t) * ui ^ 3))) from by
        simp only [η', map_add, map_mul, ← AdjoinRoot.mk_X]; rfl,
      ← Polynomial.hom_eval₂, Affine.variableChange_polynomial_inv,
      map_mul, AdjoinRoot.mk_self, mul_zero]
  let φ := AdjoinRoot.liftAlgHom W.polynomial ι η hf
  let ψ := AdjoinRoot.liftAlgHom (e • W).polynomial ι' η' hb
  exact AlgEquiv.ofAlgHom φ ψ
    (by -- φ ∘ ψ = id on (e • W).CoordinateRing
        apply AdjoinRoot.algHom_ext'
        · apply Polynomial.algHom_ext
          change φ (ψ (AdjoinRoot.of _ X)) = AdjoinRoot.of _ X
          simp only [φ, ψ, AdjoinRoot.liftAlgHom_of, ι, ι', AlgHom.comp_apply,
            IsScalarTower.toAlgHom_apply, Polynomial.aeval_X]
          rw [show (algebraMap R[X] W.CoordinateRing) = AdjoinRoot.of W.polynomial from rfl,
            AdjoinRoot.liftAlgHom_of]
          simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply]
          congr 1
          exact Affine.variableChange_aeval_comp (e := e)
        · simp only [AlgHom.comp_apply, AlgHom.id_apply, ψ, AdjoinRoot.liftAlgHom_root, η']
          simp only [φ, map_add, map_mul, AdjoinRoot.liftAlgHom_root,
            η, ι, map_neg, map_pow, map_sub]
          rw [show (algebraMap R[X] (AdjoinRoot W.polynomial)) =
            AdjoinRoot.of W.polynomial from rfl]
          simp only [AdjoinRoot.liftAlgHom_of, ι, AlgHom.comp_apply,
            IsScalarTower.toAlgHom_apply, map_add, map_mul, map_pow,
            Polynomial.aeval_C, Polynomial.aeval_X]
          simp only [C_eq_algebraMap]
          simp only [← map_pow, ← map_mul, ← map_add, ← map_neg, ← map_sub]
          change (algebraMap R[X] (AdjoinRoot (e • W).polynomial))
              ((algebraMap R R[X]) (ui ^ 3)) *
              ((algebraMap R[X] (AdjoinRoot (e • W).polynomial))
                  ((algebraMap R R[X]) (u ^ 3)) *
                  AdjoinRoot.root (e • W).polynomial +
                (algebraMap R[X] (AdjoinRoot (e • W).polynomial))
                  ((algebraMap R R[X]) (u ^ 2 * e.s) * X + (algebraMap R R[X]) e.t)) +
            (algebraMap R[X] (AdjoinRoot (e • W).polynomial))
              ((algebraMap R R[X]) (-e.s * ui ^ 3) *
                  ((algebraMap R R[X]) (u ^ 2) * X + (algebraMap R R[X]) e.r) +
                (algebraMap R R[X]) ((e.r * e.s - e.t) * ui ^ 3)) =
            AdjoinRoot.root (e • W).polynomial
          set f := algebraMap R[X] (AdjoinRoot (e • W).polynomial)
          set g := algebraMap R R[X]
          have key : f (g (ui ^ 3)) * f (g (u ^ 3)) = 1 := by
            rw [← map_mul f, ← map_mul g, ← map_one f, ← map_one g]
            congr 1; congr 1; exact pow_mul_pow_eq_one 3 e.u.inv_mul
          have residual : f (g (ui ^ 3)) * f (g (u ^ 2 * e.s) * X + g e.t) +
              f (g (-e.s * ui ^ 3) * (g (u ^ 2) * X + g e.r) +
                g ((e.r * e.s - e.t) * ui ^ 3)) = 0 := by
            rw [← map_mul f, ← map_add f, ← map_zero f]
            congr 1
            simp only [map_mul g, map_neg g, map_sub g, map_pow g]
            ring_nf
          exact mul_root_add_cancel key residual)
    (by -- ψ ∘ φ = id on W.CoordinateRing
        apply AdjoinRoot.algHom_ext'
        · apply Polynomial.algHom_ext
          change ψ (φ (AdjoinRoot.of _ X)) = AdjoinRoot.of _ X
          simp only [ψ, φ, AdjoinRoot.liftAlgHom_of, ι', ι, AlgHom.comp_apply,
            IsScalarTower.toAlgHom_apply, Polynomial.aeval_X]
          rw [show (algebraMap R[X] (e • W).CoordinateRing) =
            AdjoinRoot.of (e • W).polynomial from rfl,
            AdjoinRoot.liftAlgHom_of]
          simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply]
          congr 1
          exact Affine.variableChange_aeval_comp_inv (e := e)
        · simp only [AlgHom.comp_apply, AlgHom.id_apply]
          change ψ (φ (AdjoinRoot.root _)) = AdjoinRoot.root _
          simp only [φ, AdjoinRoot.liftAlgHom_root]
          -- Goal: ψ η = root W.polynomial
          change ψ (algebraMap R[X] _ (C (u ^ 3)) * AdjoinRoot.root _ +
            algebraMap R[X] _ (C (u ^ 2 * e.s) * X + C e.t)) = AdjoinRoot.root _
          rw [show (algebraMap R[X] (AdjoinRoot (e • W).polynomial)) =
            AdjoinRoot.of (e • W).polynomial from rfl]
          have hψ_of : ∀ r : R[X], ψ (AdjoinRoot.of _ r) = ι' r :=
            fun r => AdjoinRoot.liftAlgHom_of _ _ _ _ r
          have hψ_root : ψ (AdjoinRoot.root _) = η' :=
            AdjoinRoot.liftAlgHom_root _ _ _ _
          simp only [map_add, map_mul, hψ_of, hψ_root]
          simp only [η', ι', AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, map_add,
            map_mul, map_pow, map_neg, map_sub, Polynomial.aeval_C, Polynomial.aeval_X]
          simp only [C_eq_algebraMap]
          simp only [← map_pow, ← map_mul, ← map_add, ← map_neg, ← map_sub]
          change (algebraMap R[X] (AdjoinRoot W.polynomial))
              ((algebraMap R R[X]) (u ^ 3)) *
              ((algebraMap R[X] (AdjoinRoot W.polynomial))
                  ((algebraMap R R[X]) (ui ^ 3)) *
                  AdjoinRoot.root W.polynomial +
                (algebraMap R[X] (AdjoinRoot W.polynomial))
                  ((algebraMap R R[X]) (-e.s * ui ^ 3) * X +
                    (algebraMap R R[X]) ((e.r * e.s - e.t) * ui ^ 3))) +
            (algebraMap R[X] (AdjoinRoot W.polynomial))
              ((algebraMap R R[X]) (u ^ 2 * e.s) *
                  ((algebraMap R R[X]) (ui ^ 2) * X +
                    (algebraMap R R[X]) (-e.r * ui ^ 2)) +
                (algebraMap R R[X]) e.t) =
            AdjoinRoot.root W.polynomial
          set f := algebraMap R[X] (AdjoinRoot W.polynomial)
          set g := algebraMap R R[X]
          have key : f (g (u ^ 3)) * f (g (ui ^ 3)) = 1 := by
            rw [← map_mul f, ← map_mul g, ← map_one f, ← map_one g]
            congr 1; congr 1; exact pow_mul_pow_eq_one 3 e.u.mul_inv
          have residual : f (g (u ^ 3)) *
              f (g (-e.s * ui ^ 3) * X + g ((e.r * e.s - e.t) * ui ^ 3)) +
              f (g (u ^ 2 * e.s) * (g (ui ^ 2) * X + g (-e.r * ui ^ 2)) +
                g e.t) = 0 := by
            rw [← map_mul f, ← map_add f, ← map_zero f]
            congr 1
            simp only [map_mul g, map_neg g, map_sub g, map_pow g]
            have hu : g u * g ui = 1 := by
              rw [← map_mul g, ← map_one g]; congr 1; exact e.u.mul_inv
            linear_combination
              g e.s * (X - g e.r) * pow_mul_pow_eq_one 2 hu -
              g e.s * (X - g e.r) * pow_mul_pow_eq_one 3 hu -
              g e.t * pow_mul_pow_eq_one 3 hu
          exact mul_root_add_cancel key residual)

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
  constructor
  · intro hA
    have : IsIntegral R[X] p :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom R[X] R(X) E.FunctionField')
        (FaithfulSMul.algebraMap_injective R(X) E.FunctionField')).mp hA
    exact (isIntegrallyClosed_iff R(X)).mp inferInstance this
  · intro hB
    rcases hB with ⟨g, hg⟩
    rw [← hg, ←IsScalarTower.algebraMap_apply]
    exact isIntegral_algebraMap

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
  have hmonic : (E.polynomial.map (algebraMap R[X] R(X))).Monic := monic_polynomial.map _
  have hnd : (E.polynomial.map (algebraMap R[X] R(X))).natDegree = 2 :=
    (monic_polynomial.natDegree_map _).trans natDegree_polynomial
  let b := (AdjoinRoot.powerBasis' hmonic).basis.reindex (finCongr hnd)
  have h := b.sum_repr f
  rw [Fin.sum_univ_succ, Fin.sum_univ_one, Fin.succ_zero_eq_one] at h
  have hb0 : b 0 = 1 := by
    simp only [b, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, finCongr_symm,
      finCongr_apply_coe, Fin.val_zero, pow_zero]
  have hb1 : b 1 = AdjoinRoot.mk _ X := by
    simp only [b, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, finCongr_symm,
      finCongr_apply_coe, Fin.val_one, pow_one, AdjoinRoot.powerBasis'_gen, AdjoinRoot.root]
  rw [hb0, hb1] at h
  exact ⟨_, _, h⟩

private lemma comb_eq_mk :
    E.comb p q = AdjoinRoot.mk (E.polynomial.map (algebraMap R[X] R(X))) (C p + C q * X) := by
  simp [comb, Algebra.smul_def, AdjoinRoot.algebraMap_eq]

omit [IsDomain R] [UniqueFactorizationMonoid R] in
private lemma aeval_mk_eq {f g h : R(X)[X]} :
    aeval (AdjoinRoot.mk f h) g = AdjoinRoot.mk f (g.eval₂ C h) := by
  rw [aeval_def, show algebraMap R(X) (AdjoinRoot f) = (AdjoinRoot.mk f).comp C from rfl,
    ← hom_eval₂ g C (AdjoinRoot.mk f) h]

omit [IsDomain R] [UniqueFactorizationMonoid R] in
private lemma poly_factor :
    (X ^ 2 - C (E.trace p q) * X + C (E.norm p q)).eval₂ C (C p + C q * X) =
    C (q ^ 2) * E.polynomial.map (algebraMap R[X] R(X)) := by
  simp only [trace, norm, polynomial, Polynomial.toRatFunc]
  simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

-- If q ≠ 0, the minimal polynomial of f = p + qY is quadratic, given by Z² - Tr(f)Z + N(f).
theorem minpoly_comb (hq : q ≠ 0) :
    minpoly R(X) (E.comb p q) = X ^ 2 - C (E.trace p q) * X + C (E.norm p q) := by
  refine (minpoly.eq_of_irreducible_of_monic ?_ ?_ ?_).symm
  · -- Goal 1: Irreducible (X ^ 2 - C (E.trace p q) * X + C (E.norm p q))
    have hnd : (X ^ 2 - C (E.trace p q) * X + C (E.norm p q) : R(X)[X]).natDegree = 2 := by
      convert natDegree_quadratic (R := R(X)) (a := 1) (b := -(E.trace p q))
        (c := E.norm p q) one_ne_zero using 2
      simp only [map_neg, one_mul, C_1]; ring
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      (by rw [Finset.mem_Icc]; omega) ?_
    -- If α were a root, comb p q ∈ range(algebraMap), contradicting degree considerations.
    intro α hα
    rw [IsRoot] at hα
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hα
    have hfactor : (X ^ 2 - C (E.trace p q) * X + C (E.norm p q) : R(X)[X]) =
        (X - C α) * (X - C (E.trace p q - α)) := by
      have hnorm : E.norm p q = α * (E.trace p q - α) := by linear_combination hα
      rw [hnorm, map_mul, map_sub]; ring
    have haeval : aeval (E.comb p q) (X ^ 2 - C (E.trace p q) * X + C (E.norm p q)) = 0 := by
      rw [E.comb_eq_mk p q, aeval_mk_eq, poly_factor, map_mul, AdjoinRoot.mk_self, mul_zero]
    rw [hfactor, map_mul] at haeval
    -- One factor is zero, so comb p q = algebraMap _ _ (some root)
    have hmem : E.comb p q ∈ (algebraMap R(X) E.FunctionField').range := by
      rcases mul_eq_zero.mp haeval with h | h
      · exact ⟨α, eq_comm.mp
          (by simpa only [aeval_def, eval₂_sub, eval₂_X, eval₂_C, sub_eq_zero] using h)⟩
      · exact ⟨E.trace p q - α, eq_comm.mp
          (by simpa only [aeval_def, eval₂_sub, eval₂_X, eval₂_C, sub_eq_zero] using h)⟩
    -- But comb p q ∉ range(algebraMap): polynomial has degree 2, C p + C q * X has degree ≤ 1
    rcases hmem with ⟨r, hr⟩
    rw [comb_eq_mk] at hr
    have hdvd : E.polynomial.map (algebraMap R[X] R(X)) ∣ C p + C q * X - C r := by
      rw [← AdjoinRoot.mk_eq_zero, map_sub, sub_eq_zero]
      change AdjoinRoot.mk _ (C p + C q * X) = AdjoinRoot.of _ r
      exact hr.symm
    have hne : (C p + C q * X - C r : R(X)[X]) ≠ 0 := by
      intro h; apply hq
      have : (C p + C q * X - C r).coeff 1 = 0 := by rw [h]; simp
      simpa [coeff_sub, coeff_add, coeff_C, coeff_mul_X] using this
    have hle : (C p + C q * X - C r : R(X)[X]).natDegree ≤ 1 := by
      have heq : C p + C q * X - C r = C q * X + C (p - r) := by simp only [map_sub]; ring
      rw [heq]
      refine (natDegree_add_le _ _).trans (max_le ?_ ((natDegree_C _).le.trans (by norm_num)))
      simpa [pow_one] using natDegree_C_mul_X_pow_le q 1
    have : (E.polynomial.map (algebraMap R[X] R(X))).natDegree = 2 :=
      (monic_polynomial.natDegree_map _).trans natDegree_polynomial
    exact absurd (natDegree_le_of_dvd hdvd hne) (by omega)
  · -- Goal 2: aeval (E.comb p q) (X ^ 2 - C (E.trace p q) * X + C (E.norm p q)) = 0
    rw [E.comb_eq_mk p q, aeval_mk_eq, poly_factor, map_mul, AdjoinRoot.mk_self, mul_zero]
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
  obtain ⟨q', rfl⟩ := hq
  rw [norm] at hn
  exact (isIntegrallyClosed_iff R(X)).mp inferInstance <|
    isIntegral_of_sq_sub_mem_range
      (r₁ := q' * (C E.a₁ * X + C E.a₃))
      (r₀ := q' ^ 2 * (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆))
      (by convert hn using 1; simp [Polynomial.toRatFunc]; ring)

theorem trace_mem_of_isIntegral {p q : R(X)} (int : IsIntegral R[X] <| E.comb p q) :
    E.trace p q ∈ toRatFunc.range := by
  by_cases hq : q = 0
  · -- q = 0: comb p 0 = algebraMap _ _ p, so p ∈ range, hence trace = 2p ∈ range
    subst hq
    have hp : p ∈ toRatFunc.range := by
      have : E.comb p 0 = algebraMap _ _ p := by simp [comb, Algebra.smul_def]
      rw [this] at int
      exact (isIntegral_algebraMap_iff E).mp int
    rcases hp with ⟨f, rfl⟩
    simp only [trace]
    exact ⟨2 * f, by simp [Polynomial.toRatFunc, map_ofNat]⟩
  · -- q ≠ 0: use minpoly_comb and isIntegrallyClosed_eq_field_fractions'
    have h_min := E.minpoly_comb p q hq
    have h_eq := minpoly.isIntegrallyClosed_eq_field_fractions' R(X) int
    rw [h_min] at h_eq
    -- The degree-1 coefficient of X² - C(trace) * X + C(norm) is -trace
    -- and the degree-1 coefficient of (minpoly R[X] _).map toRatFunc is in toRatFunc.range
    have hmem : -(E.trace p q) ∈ toRatFunc.range := by
      refine ⟨(minpoly R[X] (E.comb p q)).coeff 1, ?_⟩
      have := congr_arg (·.coeff 1) h_eq
      simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_one,
        coeff_map, coeff_X_pow, coeff_C, one_ne_zero,
        OfNat.one_ne_ofNat, ↓reduceIte, zero_sub, add_zero, mul_one] at this ⊢
      exact this.symm
    rcases hmem with ⟨f, hf⟩
    exact ⟨-f, by simp [map_neg, hf]⟩

theorem norm_mem_of_isIntegral {p q : R(X)} (int : IsIntegral R[X] <| E.comb p q) :
    E.norm p q ∈ toRatFunc.range := by
  by_cases hq : q = 0
  · -- q = 0: norm p 0 = p², and p ∈ range
    subst hq
    have hp : p ∈ toRatFunc.range := by
      have : E.comb p 0 = algebraMap _ _ p := by simp [comb, Algebra.smul_def]
      rw [this] at int
      exact (isIntegral_algebraMap_iff E).mp int
    rcases hp with ⟨f, rfl⟩
    simp only [norm, mul_zero, sub_zero, zero_mul]
    exact ⟨f ^ 2, by simp [Polynomial.toRatFunc]⟩
  · -- q ≠ 0: use minpoly_comb and isIntegrallyClosed_eq_field_fractions'
    have h_min := E.minpoly_comb p q hq
    have h_eq := minpoly.isIntegrallyClosed_eq_field_fractions' R(X) int
    rw [h_min] at h_eq
    -- The degree-0 coefficient of X² - C(trace) * X + C(norm) is norm
    -- and the degree-0 coefficient of (minpoly R[X] _).map toRatFunc is in toRatFunc.range
    refine ⟨(minpoly R[X] (E.comb p q)).coeff 0, ?_⟩
    have := congr_arg (·.coeff 0) h_eq
    simp only [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C,
      coeff_map, coeff_X_zero, show (0 : ℕ) = 2 ↔ False from by decide,
      ↓reduceIte, mul_zero, sub_zero, zero_add] at this
    exact this.symm

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
  have : E.a₃ ≠ 0 := by
    rcases a₁_or_a₃_ne_zero_of_char_two E with (h1 | h3)
    · exact absurd h h1
    · exact h3
  have hmem := trace_mem_of_isIntegral E int
  simp only [trace, CharTwo.two_eq_zero, zero_mul, h, C_0, zero_add, zero_sub, neg_mem_iff,
    RingHom.mem_range] at hmem
  rcases hmem with ⟨x, hx⟩
  refine ⟨C E.a₃⁻¹ * x, ?_⟩
  rw [map_mul, hx, mul_comm (toRatFunc (C E.a₃⁻¹)), mul_assoc, ← map_mul, ← Polynomial.C_mul,
    mul_inv_cancel₀ this, C_1, map_one, mul_one]

/- If a₁ ≠ 0, we may assume it is in normal form, so that a₁ = 1 and a₃ = a₄ = 0, and
a₆ = Δ ≠ 0 by `Δ_of_isCharTwoJNeZeroNF_of_char_two`.
We can come back to prove this assuming only a₁ ≠ 0 after we've shown the coordinate ring is
integrally closed. -/
theorem right_mem_of_isIntegral_of_isCharTwoJNeZeroNF [E.IsCharTwoJNeZeroNF] :
    q ∈ toRatFunc.range := by
  have hq : q * X.toRatFunc ∈ toRatFunc.range := by
    have hmem := trace_mem_of_isIntegral E int
    rw [trace_eq_of_char_two, a₁_of_isCharTwoJNeZeroNF, a₃_of_isCharTwoJNeZeroNF,
      C_0, C_1, add_zero, one_mul] at hmem
    trivial
    -- we have Tr(p+qY) = qX in this case, so just use `trace_eq_of_char_two`
  have : IsIntegral K[X] (p * X.toRatFunc) := by
    rcases hq with ⟨qX, hqX⟩
    rcases norm_mem_of_isIntegral E int with ⟨N, hN⟩
    apply isIntegral_of_sq_sub_mem_range
      (r₁ := qX * X) (r₀ := qX ^ 2 * (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₆))
    refine ⟨X ^ 2 * N, ?_⟩
    simp only [map_mul, map_pow, map_add]
    rw [hqX, hN, norm, a₁_of_isCharTwoJNeZeroNF, a₃_of_isCharTwoJNeZeroNF,
      a₄_of_isCharTwoJNeZeroNF, C_0, C_1, one_mul, add_zero, zero_mul, add_zero]
    simp only [map_add, map_mul, map_pow]
    ring
    -- Since `E.norm p q ∈ K[X]`, we have `X² * E.norm p q ∈ K[X]` as well.
    -- Expand the definition of norm, and apply `isIntegral_of_sq_add_mem_range`
  have ⟨pX, hp⟩ : p * X.toRatFunc ∈ toRatFunc.range := by
    exact (isIntegrallyClosed_iff K(X)).mp inferInstance this
  have ⟨qX, hq⟩ := hq
  have ⟨N, hN⟩ := E.norm_mem_of_isIntegral int
  have hN : pX ^ 2 + pX * qX * X + qX ^ 2 * (X ^ 3 + C E.a₂ * X ^ 2 + C E.a₆) = X ^ 2 * N := by
    apply_fun toRatFunc using IsFractionRing.injective K[X] K(X)
    simp only [map_add, map_mul, map_pow]
    rw [hp, hq, hN, norm, a₁_of_isCharTwoJNeZeroNF, a₃_of_isCharTwoJNeZeroNF,
      a₄_of_isCharTwoJNeZeroNF, C_0, C_1, one_mul, add_zero, zero_mul, add_zero]
    simp only [map_add, map_mul, map_pow, CharTwo.sub_eq_add]
    ring
  have hsq : pX.coeff 0 ^ 2 + qX.coeff 0 ^ 2 * E.a₆ = 0 := by
    have := congr_arg (Polynomial.eval (0:K)) hN -- compare the constant term of the two sides of hN
    simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C] at this
    simp only [zero_pow two_ne_zero, zero_pow three_ne_zero, zero_mul, mul_zero,
      zero_add, add_zero] at this
    simp only [← Polynomial.coeff_zero_eq_eval_zero] at this
    exact this
  have hpx : pX.coeff 0 * qX.coeff 0 = 0 := by
    have := congr_arg (·.coeff 1) hN -- compare the X coefficient of the two sides of hN
    dsimp only at this
    simp only [coeff_add, coeff_mul] at this
    simp only [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero,
      Finset.sum_cons] at this
    simp only [Nat.dvd_one, OfNat.ofNat_ne_one, not_false_eq_true,
      coeff_sq_of_odd, Finset.sum_singleton, zero_add,
      coeff_X_one, mul_one, Finset.map_singleton,
      Function.Embedding.coe_prodMap,
      Function.Embedding.coeFn_mk, Prod.map_apply,
      Nat.succ_eq_add_one, Function.Embedding.refl_apply,
      coeff_X_zero, mul_zero, add_zero, coeff_X_pow,
      OfNat.one_ne_ofNat, ↓reduceIte, coeff_C_zero,
      mul_ite, OfNat.zero_ne_ofNat, coeff_C_succ,
      Finset.antidiagonal_zero, zero_mul, ite_mul,
      one_mul, mul_eq_zero] at this
    exact mul_eq_zero.mpr this
 -- We are in characteristic 2, so f² has no linear term for any polynomial f.
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
